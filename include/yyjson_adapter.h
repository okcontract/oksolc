// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

#ifndef SOLIDITY_YYJSON_ADAPTER_H
#define SOLIDITY_YYJSON_ADAPTER_H

#include <stddef.h>

/* Raw source-object member limit; duplicate names count toward it. */
#define SOLIDITY_JSON_MAX_SOURCE_ENTRIES 4096u

#ifdef __cplusplus
extern "C" {
#endif

typedef enum solidity_json_status
{
    SOLIDITY_JSON_OK = 0,
    SOLIDITY_JSON_SYNTAX_ERROR = 1,
    SOLIDITY_JSON_ROOT_NOT_OBJECT = 2,
    SOLIDITY_JSON_INVALID_LANGUAGE = 3,
    SOLIDITY_JSON_INVALID_SOURCES = 4,
    SOLIDITY_JSON_INVALID_SOURCE = 5,
    SOLIDITY_JSON_CALLBACK_FAILED = 6,
    SOLIDITY_JSON_OUT_OF_MEMORY = 7
} solidity_json_status;

typedef struct solidity_json_summary
{
    size_t source_count;
    size_t content_source_count;
    size_t url_source_count;
    size_t error_offset;
    int has_settings;
} solidity_json_summary;

/*
 * Called synchronously while solidity_json_inspect() owns the yyjson document.
 * name and url are borrowed, non-null-terminated byte ranges. Return 0 when a
 * URL was loaded, 1 when the next URL should be tried, and -1 to stop.
 */
typedef int (*solidity_source_url_callback)(
    void* context,
    char const* name,
    size_t name_length,
    char const* url,
    size_t url_length
);

solidity_json_status solidity_json_inspect(
    char const* input,
    size_t input_length,
    solidity_source_url_callback callback,
    void* callback_context,
    solidity_json_summary* summary
);

#ifdef __cplusplus
}
#endif

#endif
