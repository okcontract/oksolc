// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

// Validate the fields a view consumes, preserving all original fields, including
// unknown fields for complete artifact inspection. Decoders never filter rows.
export type Decoder<T> = (value: unknown) => T;
export type Decoded<D extends Decoder<unknown>> = ReturnType<D>;
export function isObject(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}
export function objectValue(value: unknown): Record<string, unknown> {
  if (!isObject(value)) throw new Error('Expected a JSON object');
  return value;
}
export function string(value: unknown): string {
  if (typeof value !== 'string') throw new Error('Expected a string');
  return value;
}
export function number(value: unknown): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) throw new Error('Expected a finite number');
  return value;
}
export function boolean(value: unknown): boolean {
  if (typeof value !== 'boolean') throw new Error('Expected a boolean');
  return value;
}
export const unknown = (value: unknown): unknown => value;
export const optional = <T>(decode: Decoder<T>): Decoder<T | undefined> => (value) => value === undefined ? value : decode(value);
export const nullable = <T>(decode: Decoder<T>): Decoder<T | null> => (value) => value === null ? value : decode(value);
export function array<T>(decode: Decoder<T>): Decoder<T[]> {
  return (value) => {
    if (!Array.isArray(value)) throw new Error('Expected an array');
    // Array.isArray's library type contains any; keep element access unknown.
    const items: unknown[] = value;
    return items.map(decode);
  };
}
type Shape = Record<string, Decoder<unknown>>;
type ObjectType<S extends Shape> = {
  [K in keyof S as undefined extends Decoded<S[K]> ? never : K]: Decoded<S[K]>
} & {
  [K in keyof S as undefined extends Decoded<S[K]> ? K : never]?: Exclude<Decoded<S[K]>, undefined>
};
export function object<S extends Shape>(shape: S): Decoder<ObjectType<S>> {
  return (value) => {
    const record = { ...objectValue(value) };
    for (const [key, decode] of Object.entries(shape)) {
      try {
        const present = Object.hasOwn(record, key);
        const field = decode(present ? record[key] : undefined);
        if (present || field !== undefined) record[key] = field;
      }
      catch (error) { throw new Error(`${key}: ${errorMessage(error)}`); }
    }
    // The loop checks every declared field, including absent optional fields.
    return record as ObjectType<S>;
  };
}
export function oneOf<const T extends readonly (string | boolean)[]>(...values: T): Decoder<T[number]> {
  return (value) => {
    for (const candidate of values) if (candidate === value) return candidate;
    throw new Error(`Expected one of ${values.join(', ')}`);
  };
}
export function parse<T>(text: string, decode: Decoder<T>): T {
  const value: unknown = JSON.parse(text);
  return decode(value);
}
export function errorMessage(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}
