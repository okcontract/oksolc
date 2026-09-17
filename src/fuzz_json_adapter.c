// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

/* ASan/UBSan mutation-fuzz target for the production yyjson adapter. */

#include "yyjson_adapter.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#define MAX_FUZZ_INPUT_BYTES (64u * 1024u)
#define LIMIT_MODE "LIMIT"
#define LIMIT_MODE_LENGTH 5u
#define REPRODUCER_DIRECTORY_SUFFIX "/f"
#define REPRODUCER_FILE_SUFFIX "/json-adapter-current-input"

typedef struct callback_state
{
    size_t calls;
    uint64_t digest;
} callback_state;

static int starts_with(
    char const* value,
    size_t value_length,
    char const* prefix
)
{
    size_t prefix_length = strlen(prefix);
    return value_length >= prefix_length &&
        memcmp(value, prefix, prefix_length) == 0;
}

static void consume_bytes(callback_state* state, char const* bytes, size_t length)
{
    size_t index;
    for (index = 0; index < length; ++index)
        state->digest = (state->digest * UINT64_C(1099511628211)) ^
            (unsigned char)bytes[index];
}

static int source_callback(
    void* context,
    char const* name,
    size_t name_length,
    char const* url,
    size_t url_length
)
{
    callback_state* state = (callback_state*)context;
    ++state->calls;
    consume_bytes(state, name, name_length);
    consume_bytes(state, url, url_length);
    if (starts_with(url, url_length, "ok:"))
        return 0;
    if (starts_with(url, url_length, "error:"))
        return -1;
    return 1;
}

static void inspect_raw(uint8_t const* data, size_t size)
{
    callback_state state = {0};
    solidity_json_summary summary;
    solidity_json_status status = solidity_json_inspect(
        (char const*)data,
        size,
        source_callback,
        &state,
        &summary
    );

    if (summary.source_count > SOLIDITY_JSON_MAX_SOURCE_ENTRIES)
        abort();
    if (status == SOLIDITY_JSON_OK &&
        summary.content_source_count + summary.url_source_count !=
            summary.source_count)
        abort();
    if (status == SOLIDITY_JSON_SYNTAX_ERROR && summary.error_offset > size)
        abort();

    /* Keep callback range reads observable without constraining fuzz results. */
    if (state.calls == SIZE_MAX && state.digest == 0)
        abort();
}

static void inspect_source_limit(uint8_t selector)
{
    size_t count = SOLIDITY_JSON_MAX_SOURCE_ENTRIES + (selector & 1u);
    size_t capacity = 64u + count * 40u;
    char* input = (char*)malloc(capacity);
    size_t offset = 0;
    size_t index;
    solidity_json_summary summary;
    solidity_json_status status;

    if (input == NULL)
        return;
    offset += (size_t)snprintf(
        input + offset,
        capacity - offset,
        "{\"language\":\"Solidity\",\"sources\":{"
    );
    for (index = 0; index < count; ++index)
    {
        int written = snprintf(
            input + offset,
            capacity - offset,
            "%s\"s%04zu\":{\"content\":\"\"}",
            index == 0 ? "" : ",",
            index
        );
        if (written < 0 || (size_t)written >= capacity - offset)
            abort();
        offset += (size_t)written;
    }
    if (capacity - offset < 3u)
        abort();
    memcpy(input + offset, "}}", 2u);
    offset += 2u;

    status = solidity_json_inspect(input, offset, NULL, NULL, &summary);
    if (status != SOLIDITY_JSON_OUT_OF_MEMORY)
    {
        if (count == SOLIDITY_JSON_MAX_SOURCE_ENTRIES)
        {
            if (status != SOLIDITY_JSON_OK || summary.source_count != count)
                abort();
        }
        else if (status != SOLIDITY_JSON_INVALID_SOURCES)
        {
            abort();
        }
    }
    free(input);
}

int LLVMFuzzerTestOneInput(uint8_t const* data, size_t size)
{
    if (size > MAX_FUZZ_INPUT_BYTES)
        return 0;
    if (size >= LIMIT_MODE_LENGTH &&
        memcmp(data, LIMIT_MODE, LIMIT_MODE_LENGTH) == 0)
    {
        uint8_t selector = size > LIMIT_MODE_LENGTH ? data[LIMIT_MODE_LENGTH] : 0;
        inspect_source_limit(selector);
    }
    else
    {
        inspect_raw(data, size);
    }
    return 0;
}

typedef struct seed_input
{
    uint8_t* bytes;
    size_t length;
} seed_input;

static uint64_t next_random(uint64_t* state)
{
    uint64_t value = *state;
    value ^= value << 13;
    value ^= value >> 7;
    value ^= value << 17;
    *state = value;
    return value;
}

static int read_seed(char const* path, seed_input* seed)
{
    FILE* file = fopen(path, "rb");
    int trailing;
    if (file == NULL)
        return 0;
    seed->bytes = (uint8_t*)malloc(MAX_FUZZ_INPUT_BYTES);
    if (seed->bytes == NULL)
    {
        fclose(file);
        return 0;
    }
    seed->length = fread(seed->bytes, 1u, MAX_FUZZ_INPUT_BYTES, file);
    trailing = fgetc(file);
    if (ferror(file) || trailing != EOF)
    {
        free(seed->bytes);
        seed->bytes = NULL;
        seed->length = 0;
        fclose(file);
        return 0;
    }
    fclose(file);
    return 1;
}

static void mutate(
    uint8_t* bytes,
    size_t* length,
    uint64_t* random_state
)
{
    static uint8_t const structural_bytes[] = {
        0, ' ', '\n', '{', '}', '[', ']', '"', ':', ',', '\\',
    };
    size_t mutation_count = 1u + (size_t)(next_random(random_state) % 16u);
    size_t mutation_index;

    for (mutation_index = 0; mutation_index < mutation_count; ++mutation_index)
    {
        uint64_t choice = next_random(random_state) % 5u;
        if (choice == 0 && *length != 0)
        {
            size_t index = (size_t)(next_random(random_state) % *length);
            bytes[index] ^= (uint8_t)(1u << (next_random(random_state) % 8u));
        }
        else if (choice == 1 && *length != 0)
        {
            size_t index = (size_t)(next_random(random_state) % *length);
            bytes[index] = (uint8_t)next_random(random_state);
        }
        else if (choice == 2 && *length < MAX_FUZZ_INPUT_BYTES)
        {
            size_t index = (size_t)(next_random(random_state) % (*length + 1u));
            memmove(bytes + index + 1u, bytes + index, *length - index);
            bytes[index] = (uint8_t)next_random(random_state);
            ++*length;
        }
        else if (choice == 3 && *length != 0)
        {
            size_t index = (size_t)(next_random(random_state) % *length);
            memmove(bytes + index, bytes + index + 1u, *length - index - 1u);
            --*length;
        }
        else if (*length != 0)
        {
            size_t index = (size_t)(next_random(random_state) % *length);
            bytes[index] = structural_bytes[
                next_random(random_state) % sizeof(structural_bytes)
            ];
        }
    }
}

static char* create_reproducer_path(void)
{
    char const* cache_root = getenv("ZIG_LOCAL_CACHE_DIR");
    size_t cache_root_length;
    size_t directory_length;
    size_t path_length;
    char* path;

    if (cache_root == NULL || cache_root[0] == '\0')
        cache_root = ".zig-cache";
    cache_root_length = strlen(cache_root);
    if (cache_root_length >
        SIZE_MAX - sizeof(REPRODUCER_DIRECTORY_SUFFIX) -
            sizeof(REPRODUCER_FILE_SUFFIX))
        return NULL;

    directory_length = cache_root_length +
        sizeof(REPRODUCER_DIRECTORY_SUFFIX) - 1u;
    path_length = directory_length + sizeof(REPRODUCER_FILE_SUFFIX) - 1u;
    path = (char*)malloc(path_length + 1u);
    if (path == NULL)
        return NULL;

    memcpy(path, cache_root, cache_root_length);
    memcpy(
        path + cache_root_length,
        REPRODUCER_DIRECTORY_SUFFIX,
        sizeof(REPRODUCER_DIRECTORY_SUFFIX)
    );
    if (mkdir(path, 0700) != 0 && errno != EEXIST)
    {
        fprintf(
            stderr,
            "failed to create reproducer directory %s: %s\n",
            path,
            strerror(errno)
        );
        free(path);
        return NULL;
    }
    memcpy(
        path + directory_length,
        REPRODUCER_FILE_SUFFIX,
        sizeof(REPRODUCER_FILE_SUFFIX)
    );
    return path;
}

static int checkpoint_reproducer(
    char const* path,
    uint8_t const* bytes,
    size_t length
)
{
    FILE* file = fopen(path, "wb");
    int saved_errno;

    if (file == NULL)
    {
        fprintf(
            stderr,
            "failed to open reproducer %s: %s\n",
            path,
            strerror(errno)
        );
        return 0;
    }
    if (length != 0 && fwrite(bytes, 1u, length, file) != length)
    {
        saved_errno = errno;
        fclose(file);
        fprintf(
            stderr,
            "failed to write reproducer %s: %s\n",
            path,
            strerror(saved_errno)
        );
        return 0;
    }
    if (fflush(file) != 0)
    {
        saved_errno = errno;
        fclose(file);
        fprintf(
            stderr,
            "failed to flush reproducer %s: %s\n",
            path,
            strerror(saved_errno)
        );
        return 0;
    }
    if (fclose(file) != 0)
    {
        fprintf(
            stderr,
            "failed to close reproducer %s: %s\n",
            path,
            strerror(errno)
        );
        return 0;
    }
    return 1;
}

int main(int argument_count, char** arguments)
{
    seed_input* seeds;
    uint8_t* mutation_buffer;
    uint64_t runs;
    uint64_t run_index;
    uint64_t random_seed;
    uint64_t random_state;
    char* runs_end = NULL;
    char* seed_end = NULL;
    char* reproducer_path = NULL;
    size_t seed_count;
    size_t seed_index;
    int exit_status = EXIT_FAILURE;

    if (argument_count < 4)
    {
        fprintf(stderr, "usage: %s RUNS RANDOM_SEED CORPUS_FILE...\n", arguments[0]);
        return EXIT_FAILURE;
    }
    errno = 0;
    runs = strtoull(arguments[1], &runs_end, 10);
    if (errno != 0 || runs_end == arguments[1] || *runs_end != '\0')
    {
        fprintf(stderr, "invalid run count: %s\n", arguments[1]);
        return EXIT_FAILURE;
    }
    errno = 0;
    random_seed = strtoull(arguments[2], &seed_end, 10);
    if (errno != 0 || seed_end == arguments[2] || *seed_end != '\0' ||
        random_seed == 0)
    {
        fprintf(stderr, "invalid nonzero random seed: %s\n", arguments[2]);
        return EXIT_FAILURE;
    }
    random_state = random_seed;

    seed_count = (size_t)argument_count - 3u;
    seeds = (seed_input*)calloc(seed_count, sizeof(*seeds));
    mutation_buffer = (uint8_t*)malloc(MAX_FUZZ_INPUT_BYTES);
    reproducer_path = create_reproducer_path();
    if (seeds == NULL || mutation_buffer == NULL || reproducer_path == NULL)
        goto cleanup;
    fprintf(
        stderr,
        "yyjson adapter sanitizer fuzz seed: %llu; active input: %s\n",
        (unsigned long long)random_seed,
        reproducer_path
    );
    for (seed_index = 0; seed_index < seed_count; ++seed_index)
    {
        if (!read_seed(arguments[seed_index + 3u], &seeds[seed_index]))
        {
            fprintf(
                stderr,
                "failed to read corpus seed: %s\n",
                arguments[seed_index + 3u]
            );
            goto cleanup;
        }
        if (!checkpoint_reproducer(
            reproducer_path,
            seeds[seed_index].bytes,
            seeds[seed_index].length
        ))
            goto cleanup;
        LLVMFuzzerTestOneInput(seeds[seed_index].bytes, seeds[seed_index].length);
    }

    for (run_index = 0; run_index < runs; ++run_index)
    {
        seed_input const* seed = &seeds[next_random(&random_state) % seed_count];
        size_t length = seed->length;
        memcpy(mutation_buffer, seed->bytes, length);
        mutate(mutation_buffer, &length, &random_state);
        if (!checkpoint_reproducer(reproducer_path, mutation_buffer, length))
            goto cleanup;
        LLVMFuzzerTestOneInput(mutation_buffer, length);
    }
    fprintf(
        stderr,
        "yyjson adapter sanitizer fuzz: %llu mutations plus %zu seeds passed\n",
        (unsigned long long)runs,
        seed_count
    );
    exit_status = EXIT_SUCCESS;

cleanup:
    if (seeds != NULL)
    {
        for (seed_index = 0; seed_index < seed_count; ++seed_index)
            free(seeds[seed_index].bytes);
    }
    free(seeds);
    free(mutation_buffer);
    free(reproducer_path);
    return exit_status;
}
