// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

#include <libsolc.h>

#include <stddef.h>
#include <string.h>

typedef struct
{
    solidity_session* session;
    int reentrant_rejections;
    int failures;
} reentrant_context;

static void reentrant_read(
    void* opaque_context,
    char const* kind,
    char const* data,
    char** contents,
    char** error_message)
{
    static char const nested_input[] =
        "{\"language\":\"Yul\",\"sources\":{\"Nested.yul\":{\"content\":"
        "\"object \\\"Nested\\\" { code { stop() } }\"}},\"settings\":"
        "{\"outputSelection\":{\"*\":{\"*\":[\"evm.bytecode.object\"]}}}}";
    static char const source[] = "contract A {}";
    reentrant_context* context = (reentrant_context*)opaque_context;
    *contents = NULL;
    *error_message = NULL;

    char* nested = solidity_session_compile(context->session, nested_input, NULL, NULL);
    if (nested == NULL)
        ++context->reentrant_rejections;
    else
    {
        ++context->failures;
        solidity_free(nested);
    }

    if (strcmp(kind, "source") != 0 || strcmp(data, "A.sol") != 0)
    {
        ++context->failures;
        return;
    }
    *contents = solidity_alloc(sizeof(source));
    if (*contents == NULL)
    {
        ++context->failures;
        return;
    }
    memcpy(*contents, source, sizeof(source));
}

int main(void)
{
    solidity_reset();

    if (strcmp(solidity_version(), "0.8.36+zig") != 0)
        return 1;
    if (strstr(solidity_license(), "GNU GENERAL PUBLIC LICENSE") == NULL)
        return 2;

    char* scratch = solidity_alloc(4);
    if (scratch == NULL)
        return 3;
    memcpy(scratch, "ok", 3);
    solidity_free(scratch);

    char const* input =
        "{\"language\":\"Yul\",\"sources\":{\"A.yul\":{\"content\":"
        "\"object \\\"A\\\" { code { stop() } }\"}},\"settings\":"
        "{\"outputSelection\":{\"*\":{\"*\":[\"evm.bytecode.object\"]}}}}";
    char* output = solidity_compile(input, NULL, NULL);
    if (output == NULL)
        return 4;
    int const valid = strstr(output, "\"object\":\"00\"") != NULL;
    solidity_free(output);

    solidity_session* session = solidity_session_create();
    if (session == NULL)
        return 6;
    char* first = solidity_session_compile(session, input, NULL, NULL);
    char* second = solidity_session_compile(session, input, NULL, NULL);
    if (first == NULL || second == NULL)
        return 7;
    if (strcmp(first, second) != 0 || strstr(second, "\"object\":\"00\"") == NULL)
        return 8;
    solidity_free(first);
    solidity_free(second);

    /* Reset output allocations without invalidating the retained session. */
    solidity_reset();
    char* after_reset = solidity_session_compile(session, input, NULL, NULL);
    if (after_reset == NULL || strstr(after_reset, "\"object\":\"00\"") == NULL)
        return 9;
    solidity_free(after_reset);

    char const* callback_input =
        "{\"language\":\"Solidity\",\"sources\":{\"A.sol\":{\"urls\":[\"A.sol\"]}},"
        "\"settings\":{\"outputSelection\":{\"*\":{\"*\":[\"abi\"]}}}}";
    reentrant_context callback_context = {session, 0, 0};
    char* callback_output = solidity_session_compile(
        session,
        callback_input,
        reentrant_read,
        &callback_context);
    if (callback_output == NULL || strstr(callback_output, "\"contracts\"") == NULL)
        return 10;
    if (callback_context.reentrant_rejections == 0 || callback_context.failures != 0)
        return 11;
    solidity_free(callback_output);

    solidity_session_destroy(session);
    solidity_session_destroy(NULL);
    solidity_reset();
    return valid ? 0 : 5;
}
