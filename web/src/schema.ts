// Runtime-checked JSON types: a schema both validates a value and gives its type,
// so the types of the server's JSON are written once.

export interface Schema<T> {
  parse(value: unknown, path?: string): T;
}

export type Infer<S> = S extends Schema<infer T> ? T : never;

export class SchemaError extends Error {
  override name = "SchemaError";
}

function fail(path: string, expected: string, value: unknown): never {
  throw new SchemaError(`${path || "value"}: expected ${expected}, got ${JSON.stringify(value)?.slice(0, 80)}`);
}

function primitive<T>(name: string, test: (v: unknown) => boolean): Schema<T> {
  return {
    parse(value, path = "") {
      if (!test(value)) fail(path, name, value);
      return value as T;
    },
  };
}

export const str = primitive<string>("a string", (v) => typeof v === "string");
export const num = primitive<number>("a number", (v) => typeof v === "number");
export const bool = primitive<boolean>("a boolean", (v) => typeof v === "boolean");
export const unknownValue = primitive<unknown>("anything", () => true);

export function lit<const T extends readonly (string | boolean)[]>(...values: T): Schema<T[number]> {
  return primitive(`one of ${values.join(", ")}`, (v) => values.includes(v as T[number]));
}

export function nullable<T>(inner: Schema<T>): Schema<T | null> {
  return { parse: (value, path = "") => (value === null ? null : inner.parse(value, path)) };
}

// For fields the server leaves out when they do not apply
export function optional<T>(inner: Schema<T>): Schema<T | undefined> {
  return { parse: (value, path = "") => (value === undefined ? undefined : inner.parse(value, path)) };
}

export function arr<T>(inner: Schema<T>): Schema<T[]> {
  return {
    parse(value, path = "") {
      if (!Array.isArray(value)) fail(path, "an array", value);
      return value.map((v, i) => inner.parse(v, `${path}[${i}]`));
    },
  };
}

type Shape = Record<string, Schema<unknown>>;
type FromShape<S extends Shape> = { [K in keyof S]: Infer<S[K]> };

// An object with these fields; fields the schema does not name are kept unchecked
export function obj<S extends Shape>(shape: S): Schema<FromShape<S>> & { shape: S } {
  return {
    shape,
    parse(value, path = "") {
      if (typeof value !== "object" || value === null || Array.isArray(value)) fail(path, "an object", value);
      const record = value as Record<string, unknown>;
      const out: Record<string, unknown> = { ...record };
      for (const [k, s] of Object.entries(shape)) {
        out[k] = s.parse(record[k], path === "" ? k : `${path}.${k}`);
      }
      return out as FromShape<S>;
    },
  };
}

export function record<T>(inner: Schema<T>): Schema<Record<string, T>> {
  return {
    parse(value, path = "") {
      if (typeof value !== "object" || value === null || Array.isArray(value)) fail(path, "an object", value);
      return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, inner.parse(v, `${path}.${k}`)]));
    },
  };
}

// The first alternative that parses
export function oneOf<A, B>(a: Schema<A>, b: Schema<B>): Schema<A | B> {
  return {
    parse(value, path = "") {
      try {
        return a.parse(value, path);
      } catch (e) {
        if (!(e instanceof SchemaError)) throw e;
        return b.parse(value, path);
      }
    },
  };
}
