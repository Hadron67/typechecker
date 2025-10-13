export function panic(msg?: string): never {
    throw new Error(msg ?? '<no further info>');
}

export function assert(cond: unknown): asserts cond {
    if (!cond) {
        panic('assertion failed');
    }
}

export function pushReversed<T, U extends T>(dest: T[], src: U[]) {
    for (let i = 0; i < src.length; i++) {
        dest.push(src[src.length - 1 - i]);
    }
}

export function popReversed<T, U extends T>(dest: U[], src: T[], length: number) {
    src.length += length;
    for (let i = 0; i < length; i++) {
        src[src.length - i - 1] = dest.pop() ?? panic();
    }
}

export function copyMap<K, V>(map: Map<K, V>): Map<K, V> {
    const ret: Map<K, V> = new Map();
    map.forEach((k, v) => ret.set(v, k));
    return ret;
}