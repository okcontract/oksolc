// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

#include "yyjson_adapter.h"
#include "yyjson.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct source_entry
{
    yyjson_val* name;
    yyjson_val* value;
    size_t ordinal;
} source_entry;

static int key_equals(yyjson_val* key, char const* expected)
{
    size_t expected_length = strlen(expected);
    return yyjson_get_len(key) == expected_length &&
        memcmp(yyjson_get_str(key), expected, expected_length) == 0;
}

/* yyjson_obj_getn() returns the first duplicate. nlohmann::json keeps the last. */
static yyjson_val* object_value_last(yyjson_val* object, char const* expected)
{
    yyjson_obj_iter iterator;
    yyjson_val* key;
    yyjson_val* value = NULL;

    if (!yyjson_is_obj(object))
        return NULL;
    iterator = yyjson_obj_iter_with(object);
    while ((key = yyjson_obj_iter_next(&iterator)) != NULL)
        if (key_equals(key, expected))
            value = yyjson_obj_iter_get_val(key);
    return value;
}

static int root_key_is_known(yyjson_val* key)
{
    return key_equals(key, "auxiliaryInput") ||
        key_equals(key, "language") ||
        key_equals(key, "settings") ||
        key_equals(key, "sources");
}

static int source_key_is_known(yyjson_val* key)
{
    return key_equals(key, "content") ||
        key_equals(key, "keccak256") ||
        key_equals(key, "urls");
}

static int object_keys_are_known(yyjson_val* object, int source_keys)
{
    yyjson_obj_iter iterator = yyjson_obj_iter_with(object);
    yyjson_val* key;
    while ((key = yyjson_obj_iter_next(&iterator)) != NULL)
    {
        if (source_keys ? !source_key_is_known(key) : !root_key_is_known(key))
            return 0;
    }
    return 1;
}

static int json_string_compare(
    char const* left,
    size_t left_length,
    char const* right,
    size_t right_length
)
{
    size_t common_length = left_length < right_length ? left_length : right_length;
    int order = memcmp(left, right, common_length);
    if (order != 0)
        return order;
    return (left_length > right_length) - (left_length < right_length);
}

static int source_entry_compare(void const* left_pointer, void const* right_pointer)
{
    source_entry const* left = (source_entry const*)left_pointer;
    source_entry const* right = (source_entry const*)right_pointer;
    int name_order = json_string_compare(
        yyjson_get_str(left->name),
        yyjson_get_len(left->name),
        yyjson_get_str(right->name),
        yyjson_get_len(right->name)
    );
    if (name_order != 0)
        return name_order;
    return (left->ordinal > right->ordinal) -
        (left->ordinal < right->ordinal);
}

/* Sort once by name and original position, then coalesce adjacent duplicates
 * with last-value-wins semantics. This matches nlohmann::json's default
 * std::map-backed object without an attacker-scalable nested scan. */
static solidity_json_status canonical_sources(
    yyjson_val* sources,
    source_entry** entries_out,
    size_t* count_out
)
{
    size_t capacity = yyjson_obj_size(sources);
    size_t count = 0;
    source_entry* entries;
    yyjson_obj_iter iterator;
    yyjson_val* name;

    *entries_out = NULL;
    *count_out = 0;
    if (capacity > SOLIDITY_JSON_MAX_SOURCE_ENTRIES)
        return SOLIDITY_JSON_INVALID_SOURCES;
    if (capacity == 0)
        return SOLIDITY_JSON_OK;
    if (capacity > SIZE_MAX / sizeof(*entries))
        return SOLIDITY_JSON_OUT_OF_MEMORY;
    entries = (source_entry*)malloc(capacity * sizeof(*entries));
    if (entries == NULL)
        return SOLIDITY_JSON_OUT_OF_MEMORY;

    iterator = yyjson_obj_iter_with(sources);
    while ((name = yyjson_obj_iter_next(&iterator)) != NULL)
    {
        entries[count].name = name;
        entries[count].value = yyjson_obj_iter_get_val(name);
        entries[count].ordinal = count;
        ++count;
    }
    qsort(entries, count, sizeof(*entries), source_entry_compare);

    {
        size_t read_index;
        size_t unique_count = 0;
        for (read_index = 0; read_index < count; ++read_index)
        {
            if (unique_count != 0 &&
                json_string_compare(
                    yyjson_get_str(entries[unique_count - 1].name),
                    yyjson_get_len(entries[unique_count - 1].name),
                    yyjson_get_str(entries[read_index].name),
                    yyjson_get_len(entries[read_index].name)
                ) == 0)
            {
                entries[unique_count - 1] = entries[read_index];
            }
            else
            {
                entries[unique_count] = entries[read_index];
                ++unique_count;
            }
        }
        count = unique_count;
    }
    *entries_out = entries;
    *count_out = count;
    return SOLIDITY_JSON_OK;
}

/* Validate the complete canonical source set before the first callback. */
static int validate_solidity_sources(source_entry const* entries, size_t count)
{
    size_t index;
    for (index = 0; index < count; ++index)
    {
        yyjson_val* source = entries[index].value;
        yyjson_val* content;
        yyjson_val* urls;
        yyjson_arr_iter url_iterator;
        yyjson_val* url;

        if (!yyjson_is_obj(source) || !object_keys_are_known(source, 1))
            return 0;
        content = object_value_last(source, "content");
        if (yyjson_is_str(content))
            continue;
        urls = object_value_last(source, "urls");
        if (!yyjson_is_arr(urls))
            return 0;
        url_iterator = yyjson_arr_iter_with(urls);
        while ((url = yyjson_arr_iter_next(&url_iterator)) != NULL)
            if (!yyjson_is_str(url))
                return 0;
    }
    return 1;
}

solidity_json_status solidity_json_inspect(
    char const* input,
    size_t input_length,
    solidity_source_url_callback callback,
    void* callback_context,
    solidity_json_summary* summary
)
{
    yyjson_read_err read_error = {0};
    yyjson_doc* document = NULL;
    yyjson_val* root;
    yyjson_val* language;
    yyjson_val* sources;
    source_entry* entries = NULL;
    size_t entry_count = 0;
    size_t source_index;
    solidity_json_status status = SOLIDITY_JSON_OK;

    if (summary == NULL)
        return SOLIDITY_JSON_INVALID_SOURCES;
    memset(summary, 0, sizeof(*summary));

    document = yyjson_read_opts(
        (char*)(void*)input,
        input_length,
        YYJSON_READ_NOFLAG,
        NULL,
        &read_error
    );
    if (document == NULL)
    {
        summary->error_offset = read_error.pos;
        if (read_error.code == YYJSON_READ_ERROR_MEMORY_ALLOCATION)
            return SOLIDITY_JSON_OUT_OF_MEMORY;
        return SOLIDITY_JSON_SYNTAX_ERROR;
    }

    root = yyjson_doc_get_root(document);
    if (!yyjson_is_obj(root))
    {
        status = SOLIDITY_JSON_ROOT_NOT_OBJECT;
        goto cleanup;
    }
    if (!object_keys_are_known(root, 0))
    {
        status = SOLIDITY_JSON_INVALID_SOURCES;
        goto cleanup;
    }

    sources = object_value_last(root, "sources");
    if (sources == NULL || yyjson_is_null(sources))
        goto cleanup;
    if (!yyjson_is_obj(sources))
    {
        status = SOLIDITY_JSON_INVALID_SOURCES;
        goto cleanup;
    }
    status = canonical_sources(sources, &entries, &entry_count);
    if (status != SOLIDITY_JSON_OK || entry_count == 0)
        goto cleanup;

    language = object_value_last(root, "language");
    if (!yyjson_equals_str(language, "Solidity") &&
        !yyjson_equals_str(language, "Yul"))
    {
        status = SOLIDITY_JSON_INVALID_LANGUAGE;
        goto cleanup;
    }

    summary->source_count = entry_count;
    summary->has_settings = object_value_last(root, "settings") != NULL;

    if (!validate_solidity_sources(entries, entry_count))
    {
        status = SOLIDITY_JSON_INVALID_SOURCE;
        goto cleanup;
    }

    for (source_index = 0; source_index < entry_count; ++source_index)
    {
        yyjson_val* source = entries[source_index].value;
        yyjson_val* content = object_value_last(source, "content");
        yyjson_val* urls;
        yyjson_arr_iter url_iterator;
        yyjson_val* url;
        int loaded = 0;

        if (yyjson_is_str(content))
        {
            ++summary->content_source_count;
            continue;
        }

        urls = object_value_last(source, "urls");
        url_iterator = yyjson_arr_iter_with(urls);
        while ((url = yyjson_arr_iter_next(&url_iterator)) != NULL)
        {
            int callback_status;
            if (callback == NULL)
                continue;
            callback_status = callback(
                callback_context,
                yyjson_get_str(entries[source_index].name),
                yyjson_get_len(entries[source_index].name),
                yyjson_get_str(url),
                yyjson_get_len(url)
            );
            if (callback_status == 0)
            {
                loaded = 1;
                break;
            }
            if (callback_status < 0)
            {
                status = SOLIDITY_JSON_CALLBACK_FAILED;
                goto cleanup;
            }
        }
        if (!loaded)
        {
            status = SOLIDITY_JSON_CALLBACK_FAILED;
            goto cleanup;
        }
        ++summary->url_source_count;
    }

cleanup:
    free(entries);
    yyjson_doc_free(document);
    return status;
}
