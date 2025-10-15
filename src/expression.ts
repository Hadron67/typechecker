import { FullSourceRange, SourceRange, UNKNOWN_SOURCERANGE, WithSourceRange } from "./parser";
import { assert, copyMap, panic, popReversed, pushReversed } from "./util";

export type Symbol = number & { __marker: Symbol };

export interface TypeAssertion {
    readonly lhs: Symbol;
    readonly rhs: Expression;
}

export interface Definition {
    readonly target: Symbol;
    readonly value: Expression;
}

export interface Module {
    readonly typeAssertions: TypeAssertion[];
    readonly definitions: Definition[];
}

export type Expression =
    | SymbolExpression
    | CallExpression
    | FunctionTypeExpression
    | LambdaExpression
    | PatternExpression
    | TypeUniverseExpression
    | LevelTypeExpression
    | PlaceholderExpression
    | LevelExpression
    | LevelSuccExpression
    | LevelMaxExpression
;

export const enum ExpressionKind {
    SYMBOL,
    LAMBDA,
    CALL,
    FN_TYPE,
    PATTERN,
    PLACEHOLDER,
    UNIVERSE,
    LEVEL_TYPE,
    LEVEL,
    LEVEL_SUCC,
    LEVEL_MAX,

    TYPE_ASSERTION,
    EQUAL,
    LESS_THAN,
    TRANSLATABLE,
}

export interface SymbolExpression extends SourceRange {
    readonly kind: ExpressionKind.SYMBOL;
    readonly symbol: Symbol;
}

export interface CallExpression {
    readonly kind: ExpressionKind.CALL;
    readonly fn: Expression;
    readonly args: Expression[];
}

export interface FunctionTypeExpression {
    readonly kind: ExpressionKind.FN_TYPE;
    readonly inputType: Expression;
    readonly outputType: Expression;
    readonly arg?: Symbol; // if this is non-undefined, it's a dependent function type
}

export interface LambdaExpression {
    readonly kind: ExpressionKind.LAMBDA;
    readonly body: Expression;
    readonly arg: Symbol;
}

export interface PatternExpression {
    readonly kind: ExpressionKind.PATTERN;
    readonly variable?: Symbol;
}

export interface TypeUniverseExpression {
    readonly kind: ExpressionKind.UNIVERSE;
    readonly subscript: Expression;
}

export interface PlaceholderExpression {
    readonly kind: ExpressionKind.PLACEHOLDER;
}

export interface LevelTypeExpression {
    readonly kind: ExpressionKind.LEVEL_TYPE;
}

export interface LevelSuccExpression {
    readonly kind: ExpressionKind.LEVEL_SUCC;
    readonly expr: Expression;
}

export interface LevelMaxExpression {
    readonly kind: ExpressionKind.LEVEL_MAX;
    readonly lhs: Expression;
    readonly rhs: Expression;
}

export interface LevelExpression {
    readonly kind: ExpressionKind.LEVEL;
    readonly value: number;
}

export interface TypeAssertionExpression {
    readonly kind: ExpressionKind.TYPE_ASSERTION;
    readonly expr: Expression;
    readonly type: Expression;
}

export interface EqualExpression {
    readonly kind: ExpressionKind.EQUAL;
    readonly lhs: Expression;
    readonly rhs: Expression;
}

export interface LessThanExpression {
    readonly kind: ExpressionKind.LESS_THAN;
    readonly lhs: Expression;
    readonly rhs: Expression;
}

export type DisplayExpression =
    | Expression
    | TypeAssertionExpression
    | EqualExpression
    | LessThanExpression
    ;

export const LEVEL_TYPE: LevelTypeExpression = {kind: ExpressionKind.LEVEL_TYPE};

export interface ExpressionRule {
    readonly lhs: Expression;
    readonly rhs: Expression;
}

export interface VariableInfo {
    type?: Expression;
    ownValue?: Expression;
    readonly downValue: [Expression, Expression][];
}

export interface SymbolEntry {
    readonly name: string;
    readonly parent: Symbol | null;
    readonly isLocal: boolean;
    subSymbols?: Map<string, Symbol>;
    type?: Expression;
    ownValue?: Expression;
    downValue?: [Expression, Expression][];
}

export class SymbolRegistry {
    private readonly entriesById: SymbolEntry[] = [];
    private readonly entriesByName: Map<string, Symbol> = new Map();
    private readonly removedSymbols: Symbol[] = [];

    defineInternalSymbols() {
        const builtin = this.addNewSymbol(null, "builtin", false)[0];
        const level = this.addNewSymbol(builtin, "Level", false)[0];
        this.getSymbolEntry(level).ownValue = {kind: ExpressionKind.LEVEL_TYPE};
    }
    getSymbolCount() {
        return this.entriesById.length;
    }
    getSymbolEntry(s: Symbol): SymbolEntry {
        return this.tryGetSymbolEntry(s) ?? panic();
    }
    getSymbolName(s: Symbol) {
        return this.tryGetSymbolEntry(s) ?? `$${s - this.entriesById.length}`;
    }
    tryGetSymbolEntry(s: Symbol): SymbolEntry | null {
        if (s >= 0 && s < this.entriesById.length) {
            return this.entriesById[s];
        } else return null;
    }
    stringifySymbol(symbol: Symbol) {
        const entry0 = this.tryGetSymbolEntry(symbol);
        if (entry0 !== null) {
            if (entry0.isLocal) return entry0.name;
            let s: Symbol | null = symbol;
            const path: string[] = [];
            while (s !== null) {
                const entry = this.getSymbolEntry(s);
                path.unshift(entry.name);
                s = entry.parent;
            }
            return path.join('.');
        } else {
            return `$${symbol - this.entriesById.length}`;
        }
    }
    private createSymbol(parent: Symbol | null, name: string, isLocal: boolean) {
        let ret: Symbol;
        if (this.removedSymbols.length > 0) {
            ret = this.removedSymbols.pop()! as Symbol;
            this.entriesById[ret] = {parent, name, isLocal};
        } else {
            ret = this.entriesById.length as Symbol;
            this.entriesById.push({parent, name, isLocal});
        }
        if (parent !== null) {
            const entry = this.entriesById[parent];
            if (entry.subSymbols === void 0) {
                entry.subSymbols = new Map();
            }
            entry.subSymbols.set(name, ret);
        } else {
            this.entriesByName.set(name, ret);
        }
        return ret;
    }
    addNewSymbol(parent: Symbol | null, name: string, isLocal: boolean): [Symbol, boolean] {
        let map = parent === null ? this.entriesByName : this.entriesById[parent].subSymbols;
        if (map !== void 0 && map.has(name)) {
            return [map.get(name)!, false];
        } else {
            const ret = this.createSymbol(parent, name, isLocal);
            return [ret, true];
        }
    }
    getSymbol(parent: Symbol | null, name: string, create: boolean): Symbol | null {
        const map = parent === null ? this.entriesByName : this.entriesById[parent].subSymbols;
        if (map !== void 0 && map.has(name)) {
            return map.get(name)!;
        } else if (create) {
            return this.addNewSymbol(parent, name, false)[0];
        } else return null;
    }
    removeSymbol(symbol: Symbol) {
        const entry = this.getSymbolEntry(symbol);
        if (entry.parent !== null) {
            const parent = this.getSymbolEntry(entry.parent);
            (parent.subSymbols ?? panic()).delete(entry.name);
        }
        this.removedSymbols.push(symbol);
    }
    dump() {
        const lines: string[] = [];
        const stack: Symbol[] = [];
        pushReversed(stack, Array.from(this.entriesByName.values()));
        while (stack.length > 0) {
            const s = stack.pop()!;
            const entry = this.getSymbolEntry(s);
            const {type, ownValue, downValue} = entry;
            if (type !== void 0) {
                lines.push(`${this.stringifySymbol(s)}: ${inputForm(this, type)}`);
            }
            if (ownValue !== void 0) {
                lines.push(`${this.stringifySymbol(s)} = ${inputForm(this, ownValue)}`);
            }
            if (downValue !== void 0) {
                for (const [lhs, rhs] of downValue) {
                    lines.push(inputForm(this, lhs) + ' := ' + inputForm(this, rhs));
                }
            }
            if (entry.subSymbols) {
                pushReversed(stack, Array.from(entry.subSymbols.values()));
            }
        }
        return lines;
    }
}
export class TempSymbolRegistry {
    private readonly tempSymbols: SymbolEntry[] = [];
    constructor(readonly parent: SymbolRegistry) {}
    getSymbolEntry(s: Symbol) {
        const count = this.parent.getSymbolCount();
        if (s < count) {
            return this.parent.getSymbolEntry(s);
        } else {
            return this.tempSymbols[s - count];
        }
    }
    isTempSymbol(s: Symbol) {
        return s >= this.parent.getSymbolCount();
    }
    createTempSymbol(isLocal: boolean, type: Expression | null) {
        const ret = this.tempSymbols.length + this.parent.getSymbolCount() as Symbol;
        const entry: SymbolEntry = { name: '', parent: null, isLocal };
        if (type !== null) {
            entry.type = type;
        }
        this.tempSymbols.push(entry);
        return ret;
    }
    forEachTempSymbol(cb: (s: Symbol, entry: SymbolEntry) => void) {
        const count = this.parent.getSymbolCount();
        for (let i = 0, a = this.tempSymbols; i < a.length; i++) {
            cb(i + count as Symbol, a[i]);
        }
    }
}

export function matchPattern(expr: Expression, pattern: Expression) {
    const substitues: Map<Symbol, Expression> = new Map();
    const todo: [Expression, Expression][] = [[pattern, expr]];
    while (todo.length > 0) {
        const [pattern, expr] = todo.pop()!;
        switch (pattern.kind) {
            case ExpressionKind.SYMBOL: {
                if (expr.kind !== ExpressionKind.SYMBOL) return null;
                if (pattern.symbol !== expr.symbol) return null;
                break;
            }
            case ExpressionKind.PATTERN:
                if (pattern.variable !== void 0) {
                    const old = substitues.get(pattern.variable);
                    if (old !== void 0) {
                        todo.push([old, expr]);
                    } else {
                        substitues.set(pattern.variable, expr);
                    }
                }
                break;
            case ExpressionKind.CALL:
                if (expr.kind !== ExpressionKind.CALL) return null;
                if (expr.args.length !== pattern.args.length) {
                    return null;
                }
                for (let i = 0, a = pattern.args, b = expr.args; i < a.length; i++) {
                    todo.push([a[a.length - 1 - i], b[b.length - 1 - i]]);
                }
                todo.push([pattern.fn, expr.fn]);
                break;
            case ExpressionKind.LAMBDA: {
                if (expr.kind !== ExpressionKind.LAMBDA) return null;
                todo.push([pattern.body, expr.arg !== pattern.arg ? replaceOneSymbol(expr.body, expr.arg, symbolExpression(pattern.arg, null)) : expr.body]);
                break;
            }
            case ExpressionKind.FN_TYPE:
                if (expr.kind !== ExpressionKind.FN_TYPE) return null;
                todo.push(
                    [pattern.outputType, pattern.arg !== void 0 && expr.arg !== void 0 && pattern.arg !== expr.arg ? replaceOneSymbol(expr.outputType, expr.arg, pattern) : expr.outputType],
                    [pattern.inputType, expr.inputType],
                );
                break;
            case ExpressionKind.UNIVERSE:
                if (expr.kind !== ExpressionKind.UNIVERSE) return null;
                todo.push([pattern.subscript, expr.subscript]);
                break;
            case ExpressionKind.LEVEL_TYPE:
                if (expr.kind !== ExpressionKind.LEVEL_TYPE) return null;
                break;
            case ExpressionKind.LEVEL_SUCC:
                if (expr.kind === ExpressionKind.LEVEL_SUCC) {
                    todo.push([pattern.expr, expr.expr]);
                } else if (expr.kind === ExpressionKind.LEVEL) {
                    if (expr.value > 0) {
                        todo.push([pattern.expr, {kind: ExpressionKind.LEVEL, value: expr.value - 1}]);
                    } else return null;
                }
                break;
            default: panic();
        }
    }
    return substitues;
}

function makeSymbolMap(map: Map<Symbol, Symbol>, symbol1: Symbol | undefined, symbol2: Symbol | undefined) {
    if (symbol2 !== void 0 && symbol1 !== void 0) {
        if (symbol2 !== symbol1 || map.has(symbol2)) {
            map = copyMap(map);
            if (symbol1 !== symbol2) {
                map.set(symbol2, symbol1);
            } else {
                map.delete(symbol2);
            }
        }
    } else if (symbol2 !== void 0 && map.has(symbol2)) {
        map = copyMap(map);
        map.delete(symbol2);
    }
    return map;
}

type ExpanderAction = (self: Expander) => void;
export class Expander {
    private readonly todo: ExpanderAction[] = [];
    private readonly stack: Expression[] = [];
    private changed = false;
    constructor(private readonly registry: TempSymbolRegistry) {}
    private doActions(...actions: ExpanderAction[]) {
        pushReversed(this.todo, actions);
    }
    private _expand(expr: Expression): ExpanderAction {
        return self => {
            switch (expr.kind) {
                case ExpressionKind.SYMBOL: {
                    const entry = self.registry.getSymbolEntry(expr.symbol);
                    const ownValue = entry.ownValue;
                    if (ownValue !== void 0) {
                        self.doActions(self._expand(ownValue));
                    } else self.stack.push(expr);
                    return;
                }
                case ExpressionKind.CALL: {
                    self.doActions(self._expandCall(expr.fn, expr.args));
                    return;
                }
                case ExpressionKind.LAMBDA: {
                    const arg = expr.arg;
                    self.doActions(self._expand(expr.body), self => {
                        if (self.changed) {
                            self.stack.push({kind: ExpressionKind.LAMBDA, arg, body: self.stack.pop()!});
                        } else {
                            self.stack.push(expr);
                        }
                    });
                    return;
                }
                case ExpressionKind.FN_TYPE: {
                    const arg = expr.arg;
                    self.doActions(self._expand(expr.inputType), self._expand(expr.outputType), self => {
                        const outputType = self.stack.pop()!;
                        const inputType = self.stack.pop()!;
                        self.stack.push({kind: ExpressionKind.FN_TYPE, inputType, outputType, arg});
                    });
                    return;
                }
                case ExpressionKind.UNIVERSE: {
                    self.doActions(self._expand(expr.subscript), self => {
                        self.stack.push({kind: ExpressionKind.UNIVERSE, subscript: self.stack.pop()!});
                    });
                    return;
                }
                case ExpressionKind.LEVEL_SUCC: {
                    self.doActions(self._expand(expr.expr), self => {
                        const expr = self.stack.pop()!;
                        if (expr.kind === ExpressionKind.LEVEL) {
                            self.changed = true;
                            self.stack.push({kind: ExpressionKind.LEVEL, value: expr.value + 1});
                        } else {
                            self.stack.push({kind: ExpressionKind.LEVEL_SUCC, expr});
                        }
                    });
                    break;
                }
                case ExpressionKind.LEVEL_MAX: {
                    self.doActions(self._expand(expr.lhs), self._expand(expr.rhs), self => {
                        const rhs = self.stack.pop()!;
                        const lhs = self.stack.pop()!;
                        if (lhs.kind === ExpressionKind.LEVEL && rhs.kind === ExpressionKind.LEVEL) {
                            self.changed = true;
                            self.stack.push({kind: ExpressionKind.LEVEL, value: Math.max(lhs.value, rhs.value)});
                        } else {
                            self.stack.push({kind: ExpressionKind.LEVEL_MAX, lhs, rhs});
                        }
                    });
                    break;
                }
                case ExpressionKind.PATTERN:
                case ExpressionKind.LEVEL_TYPE:
                case ExpressionKind.LEVEL:
                case ExpressionKind.PLACEHOLDER: self.stack.push(expr); return;
                default: panic();
            }
        };
    }
    private _expandCall(fn: Expression, args: Expression[]): ExpanderAction {
        return self => {
            if (args.length === 1) {
                self.doActions(self._expand(fn), self._expand(args[0]), self => {
                    const arg = self.stack.pop()!;
                    const fn = self.stack.pop()!;
                    let result: Expression;
                    switch (fn.kind) {
                        case ExpressionKind.LAMBDA: {
                            result = replaceOneSymbol(fn, fn.arg, arg);
                            self.changed = true;
                            break;
                        }
                        case ExpressionKind.CALL: {
                            result = {kind: ExpressionKind.CALL, fn: fn.fn, args: fn.args.concat([arg])};
                            break;
                        }
                        default: result = {kind: ExpressionKind.CALL, fn, args: [arg]};
                    }
                    if (result.kind === ExpressionKind.CALL && result.fn.kind === ExpressionKind.SYMBOL) {
                        const entry = self.registry.getSymbolEntry(result.fn.symbol);
                        if (entry.downValue !== void 0) {
                            for (const [lhs, rhs] of entry.downValue) {
                                const map = matchPattern(result, lhs);
                                if (map !== null) {
                                    self.changed = true;
                                    result = replaceSymbols(rhs, map);
                                    self.doActions(self._expand(result));
                                    return;
                                }
                            }
                        }
                    }
                    self.stack.push(result);
                });
            } else {
                const lastArg = args[args.length - 1];
                self.doActions(self._expandCall(fn, args.slice(-1)), self => {
                    self._expandCall(self.stack.pop()!, [lastArg]);
                });
            }
        };
    }
    expand(expr: Expression): [Expression, boolean] {
        this.changed = false;
        this.doActions(this._expand(expr));
        while (this.todo.length > 0) {
            this.todo.pop()!(this);
        }
        assert(this.stack.length === 1);
        return [this.stack.pop()!, this.changed];
    }
}

export function visitExpression(expr: Expression, cb: (expr: Expression) => boolean) {
    const todo = [expr];
    while (todo.length > 0) {
        const t = todo.pop()!;
        switch (t.kind) {
            case ExpressionKind.LEVEL:
            case ExpressionKind.PLACEHOLDER:
            case ExpressionKind.LEVEL_TYPE:
            case ExpressionKind.PATTERN:
            case ExpressionKind.SYMBOL: if (cb(t)) return false; break;
            case ExpressionKind.CALL:
                if (cb(t)) return false;
                pushReversed(todo, t.args);
                todo.push(t.fn);
                break;
            case ExpressionKind.LAMBDA:
                if (cb(t)) return false;
                todo.push(t.body);
                break;
            case ExpressionKind.UNIVERSE:
                if (cb(t)) return false;
                todo.push(t.subscript);
                break;
            case ExpressionKind.FN_TYPE:
                if (cb(t)) return false;
                todo.push(t.outputType, t.inputType);
                break;
        }
    }
}

export function symbolExpression(symbol: Symbol, loc: FullSourceRange | null): SymbolExpression {
    return {kind: ExpressionKind.SYMBOL, symbol, ...(loc ?? UNKNOWN_SOURCERANGE)};
}

function stringifySymbolMap(context: SymbolRegistry, map: Map<Symbol, Expression>) {
    const parts: string[] = [];
    map.forEach((v, k) => {
        parts.push(`${context.stringifySymbol(k)} === ${inputForm(context, v)}`);
    });
    return `{${parts.join(', ')}}`;
}

function expandLambdaCalls(expr: Expression): [Expression, boolean] {
    if (expr.kind === ExpressionKind.CALL && expr.fn.kind === ExpressionKind.LAMBDA) {
        const maps = new Map<Symbol, Expression>();
        let argCount = 0;
        let fn: Expression = expr.fn;
        while (fn.kind === ExpressionKind.LAMBDA && argCount < expr.args.length) {
            maps.set(fn.arg, expr.args[argCount]);
            argCount++;
            fn = fn.body;
        }
        fn = replaceSymbols(fn, maps);
        if (argCount === expr.args.length) {
            return [fn, true];
        } else if (fn.kind === ExpressionKind.CALL) {
            return [{kind: ExpressionKind.CALL, fn: fn.fn, args: fn.args.concat(expr.args.slice(argCount))}, true];
        }
    }
    return [expr, false];
}

type ReplacerAction = (self: Replacer) => void;

class Replacer {
    private readonly maps: Map<Symbol, Expression> = new Map();
    private readonly todo: ReplacerAction[] = [];
    private readonly stack: Expression[] = [];
    private _doActions(...actions: ReplacerAction[]) {
        pushReversed(this.todo, actions);
    }
    private _replace(expr: Expression): ReplacerAction {
        return self => {
            switch (expr.kind) {
                case ExpressionKind.SYMBOL: {
                    const value = self.maps.get(expr.symbol);
                    if (value !== void 0) {
                        self.stack.push(value);
                    } else {
                        self.stack.push(expr);
                    }
                    break;
                }
                case ExpressionKind.FN_TYPE: {
                    if (expr.arg === void 0 || !self.maps.has(expr.arg)) {
                        const arg = expr.arg;
                        self._doActions(this._replace(expr.inputType), self._replace(expr.outputType), self => {
                            const outputType = self.stack.pop()!;
                            const inputType = self.stack.pop()!;
                            self.stack.push({kind: ExpressionKind.FN_TYPE, inputType, outputType, arg});
                        });
                    } else {
                        const arg = expr.arg;
                        const old = self.maps.get(expr.arg) ?? panic();
                        self._doActions(self._replace(expr.inputType), self => {
                            self.maps.delete(arg);
                        }, self._replace(expr.outputType), self => {
                            self.maps.set(arg, old);
                            const outputType = self.stack.pop()!;
                            const inputType = self.stack.pop()!;
                            self.stack.push({kind: ExpressionKind.FN_TYPE, inputType, outputType, arg});
                        });
                    }
                    break;
                }
                case ExpressionKind.LAMBDA: {
                    const arg = expr.arg;
                    if (!self.maps.has(expr.arg)) {
                        self._doActions(self._replace(expr.body), self => {
                            self.stack.push({kind: ExpressionKind.LAMBDA, arg, body: self.stack.pop()!});
                        });
                    } else {
                        const old = self.maps.get(arg) ?? panic();
                        self._doActions(self._replace(expr.body), self => {
                            self.maps.set(arg, old);
                            self.stack.push({kind: ExpressionKind.LAMBDA, arg, body: self.stack.pop()!});
                        });
                    }
                    break;
                }
                case ExpressionKind.CALL: {
                    const length = expr.args.length;
                    self._doActions(self._replace(expr.fn), ...expr.args.map(arg => self._replace(arg)), self => {
                        const args: Expression[] = [];
                        popReversed(self.stack, args, length);
                        const fn = self.stack.pop()!;
                        self.stack.push({kind: ExpressionKind.CALL, fn, args});
                    });
                    break;
                }
                case ExpressionKind.UNIVERSE: {
                    self._doActions(self._replace(expr.subscript), self => {
                        self.stack.push({kind: ExpressionKind.UNIVERSE, subscript: self.stack.pop()!});
                    });
                    break;
                }
                default: self.stack.push(expr);
            }
        };
    }
    private doReplace(expr: Expression) {
        this._doActions(this._replace(expr));
        while (this.todo.length > 0) {
            this.todo.pop()!(this);
        }
        assert(this.stack.length === 1);
        return this.stack.pop()!;
    }
    replaceOne(expr: Expression, source: Symbol, replacement: Expression) {
        this.maps.clear();
        this.maps.set(source, replacement);
        return this.doReplace(expr);
    }
    replaceMany(expr: Expression, map: Map<Symbol, Expression>) {
        this.maps.clear();
        map.forEach((v, k) => this.maps.set(k, v));
        return this.doReplace(expr);
    }
}

export function replaceOneSymbol(expr: Expression, source: Symbol, replacement: Expression) {
    return new Replacer().replaceOne(expr, source, replacement);
}

export function replaceSymbols(expr: Expression, map: Map<Symbol, Expression>) {
    return new Replacer().replaceMany(expr, map);
}

export function toPlainString(context: SymbolRegistry, str: ExpressionMessage) {
    let ret = '';
    for (const s of str) {
        if (typeof s === 'string') {
            ret += s;
        } else ret += inputForm(context, s);
    }
    return ret;
}

export function inputForm(context: SymbolRegistry, expr: DisplayExpression) {
    const stack: string[] = [];
    const todo: (DisplayExpression | ((stack: string[]) => void))[] = [expr];
    while (todo.length > 0) {
        const t = todo.pop()!;
        if (typeof t === 'function') {
            t(stack);
        } else switch (t.kind) {
            case ExpressionKind.EQUAL:
                todo.push(stack => {
                    const rhs = stack.pop()!;
                    const lhs = stack.pop()!;
                    stack.push(`${lhs} === ${rhs}`);
                }, t.rhs, t.lhs);
                break;
            case ExpressionKind.TYPE_ASSERTION:
                todo.push(stack => {
                    const expr = stack.pop()!;
                    const type = stack.pop()!;
                    stack.push(`${expr} : ${type}`);
                }, t.expr, t.type);
                break;
            case ExpressionKind.LESS_THAN:
                todo.push(stack => {
                    const rhs = stack.pop()!;
                    const lhs = stack.pop()!;
                    stack.push(`${lhs} < ${rhs}`);
                }, t.rhs, t.lhs);
                break;
            case ExpressionKind.SYMBOL: stack.push(context.stringifySymbol(t.symbol)); break;
            case ExpressionKind.FN_TYPE: {
                const needsParenth = t.inputType.kind === ExpressionKind.FN_TYPE;
                const arg = t.arg;
                todo.push(stack => {
                    const outputType = stack.pop()!;
                    const inputType = stack.pop()!;
                    if (arg !== void 0) {
                        const name = context.getSymbolName(arg);
                        stack.push(`(${name}: ${inputType}) -> ${outputType}`);
                    } else if (needsParenth) {
                        stack.push(`(${inputType}) -> ${outputType}`);
                    } else stack.push(`${inputType} -> ${outputType}`);
                }, t.outputType, t.inputType);
                break;
            }
            case ExpressionKind.LAMBDA: {
                const arg = t.arg;
                todo.push(stack => {
                    const body = stack.pop()!;
                    stack.push(`\\${context.getSymbolName(arg)} ${body}`);
                }, t.body);
                break;
            }
            case ExpressionKind.PATTERN: {
                if (t.variable !== void 0) {
                    stack.push(`?${context.getSymbolName(t.variable)}`);
                } else {
                    stack.push('?');
                }
                break;
            }
            case ExpressionKind.CALL: {
                const length = t.args.length;
                todo.push(stack => {
                    const args: string[] = [];
                    popReversed(stack, args, length);
                    const fn = stack.pop()!;
                    stack.push(`${fn}(${args.join(', ')})`);
                });
                pushReversed(todo, t.args);
                todo.push(t.fn);
                break;
            }
            case ExpressionKind.PLACEHOLDER: {
                stack.push('_');
                break;
            }
            case ExpressionKind.UNIVERSE: {
                todo.push(stack => {
                    stack.push(`type(${stack.pop()!})`);
                }, t.subscript);
                break;
            }
            case ExpressionKind.LEVEL_SUCC: {
                todo.push(stack => {
                    stack.push(`builting.Level.succ(${stack.pop()!})`);
                }, t.expr);
                break;
            }
            case ExpressionKind.LEVEL_MAX: {
                todo.push(stack => {
                    const rhs = stack.pop()!;
                    const lhs = stack.pop()!;
                    stack.push(`builting.Level.succ(${lhs}, ${rhs})`);
                }, t.rhs, t.lhs);
                break;
            }
            case ExpressionKind.LEVEL_TYPE: stack.push('builtin.Level'); break;
            case ExpressionKind.LEVEL: stack.push(`${t.value.toString()}l`); break;
            default: panic();
        }
    }
    assert(stack.length === 1);
    return stack[0];
}

export type ExpressionMessage = (string | DisplayExpression)[];

export interface ExpressionLogger {
    info(context: SymbolRegistry, msg: () => ExpressionMessage): void;
}

export class ConsoleLogger implements ExpressionLogger {
    info(context: SymbolRegistry, msg: () => ExpressionMessage): void {
        console.log(toPlainString(context, msg()));
    }
}
