import { FullSourceRange, SourceRange, WithSourceRange } from "./parser";
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
    | UniverseSubscriptType
    | PlaceholderExpression
    | TypeUniverseSubscriptExpression
;

export const enum ExpressionKind {
    SYMBOL,
    LAMBDA,
    CALL,
    FN_TYPE,
    PATTERN,
    TYPE_UNIVERSE,
    UNIVERSE_SUBSCRIPT_TYPE,
    UNIVERSE_SUBSCRIPT,
    PLACEHOLDER,
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
    readonly kind: ExpressionKind.TYPE_UNIVERSE;
    readonly subscript: Expression;
}

export interface PlaceholderExpression {
    readonly kind: ExpressionKind.PLACEHOLDER;
}

export interface UniverseSubscriptType {
    readonly kind: ExpressionKind.UNIVERSE_SUBSCRIPT_TYPE;
}

export interface TypeUniverseSubscriptExpression {
    readonly kind: ExpressionKind.UNIVERSE_SUBSCRIPT;
    readonly value: number;
}

export const UNIVERSE_SUBSCRIPT_TYPE: UniverseSubscriptType = {kind: ExpressionKind.UNIVERSE_SUBSCRIPT_TYPE};

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
    readonly subSymbols: Map<string, Symbol>;
    info?: VariableInfo;
}

export class SymbolRegistry {
    private readonly entriesById: SymbolEntry[] = [];
    private readonly entriesByName: Map<string, Symbol> = new Map();
    private readonly removedSymbols: Symbol[] = [];

    defineInternalSymbols() {
        const typen = this.getSymbolEntry(this.addNewSymbol(null, "typen")[0]);
        typen.info = {ownValue: {kind: ExpressionKind.UNIVERSE_SUBSCRIPT_TYPE}, downValue: []};
    }
    getSymbolEntry(s: Symbol): SymbolEntry {
        assert(s >= 0 && s < this.entriesById.length);
        return this.entriesById[s] ?? panic();
    }
    stringifySymbol(symbol: Symbol) {
        let s: Symbol | null = symbol;
        const path: string[] = [];
        while (s !== null) {
            const entry = this.getSymbolEntry(s);
            path.unshift(entry.name);
            s = entry.parent;
        }
        return path.join('.');
    }
    addNewSymbol(parent: Symbol | null, name: string): [Symbol, boolean] {
        const map = parent === null ? this.entriesByName : this.entriesById[parent].subSymbols;
        if (map.has(name)) {
            return [map.get(name)!, false];
        } else if (this.removedSymbols.length > 0) {
            const ret = this.removedSymbols.pop()! as Symbol;
            this.entriesById[ret] = {
                parent,
                name,
                subSymbols: new Map(),
            };
            map.set(name, ret);
            if (parent !== null) {
                this.entriesById[parent].subSymbols.set(name, ret);
            }
            return [ret, true];
        } else {
            const ret = this.entriesById.length as Symbol;
            this.entriesById.push({
                parent,
                name,
                subSymbols: new Map(),
            });
            map.set(name, ret);
            if (parent !== null) {
                this.entriesById[parent].subSymbols.set(name, ret);
            }
            return [ret, true];
        }
    }
    getSymbol(parent: Symbol | null, name: string, create: boolean): Symbol | null {
        const map = parent === null ? this.entriesByName : this.entriesById[parent].subSymbols;
        if (map.has(name)) {
            return map.get(name)!;
        } else if (create) {
            return this.addNewSymbol(parent, name)[0];
        } else return null;
    }
    removeSymbol(symbol: Symbol) {
        const entry = this.getSymbolEntry(symbol);
        if (entry.parent !== null) {
            const parent = this.getSymbolEntry(entry.parent);
            parent.subSymbols.delete(entry.name);
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
            const type = entry.info?.type;
            const ownValue = entry.info?.ownValue;
            if (type !== void 0) {
                lines.push(`${this.stringifySymbol(s)}: ${inputForm(this, type)}`);
            }
            if (ownValue !== void 0) {
                lines.push(`${this.stringifySymbol(s)} = ${inputForm(this, ownValue)}`);
            }
            const downValue = entry.info?.downValue;
            if (downValue !== void 0) {
                for (const [lhs, rhs] of downValue) {
                    lines.push(inputForm(this, lhs) + ' := ' + inputForm(this, rhs));
                }
            }
            pushReversed(stack, Array.from(entry.subSymbols.values()));
        }
        return lines;
    }
}

export function matchPattern(expr: Expression, pattern: Expression) {
    const substitues: Map<Symbol, Expression> = new Map();
    const todo: [Expression, Expression, Map<Symbol, Symbol>][] = [[pattern, expr, new Map()]];
    while (todo.length > 0) {
        const [pattern, expr, symbolMaps] = todo.pop()!;
        switch (pattern.kind) {
            case ExpressionKind.SYMBOL: {
                if (expr.kind !== ExpressionKind.SYMBOL) return null;
                const mapped = symbolMaps.has(expr.symbol) ? symbolMaps.get(expr.symbol) : expr.symbol;
                if (pattern.symbol !== mapped) return null;
                break;
            }
            case ExpressionKind.PATTERN:
                if (pattern.variable !== void 0) {
                    const old = substitues.get(pattern.variable);
                    if (old !== void 0) {
                        todo.push([old, expr, symbolMaps]);
                    } else {
                        substitues.set(pattern.variable, expr);
                    }
                }
                break;
            case ExpressionKind.CALL:
                if (typeof expr !== 'object' || expr.kind !== ExpressionKind.CALL) return null;
                if (expr.args.length !== pattern.args.length) {
                    return null;
                }
                for (let i = 0, a = pattern.args, b = expr.args; i < a.length; i++) {
                    todo.push([a[a.length - 1 - i], b[b.length - 1 - i], symbolMaps]);
                }
                todo.push([pattern.fn, expr.fn, symbolMaps]);
                break;
            case ExpressionKind.LAMBDA: {
                if (typeof expr !== 'object' || expr.kind !== ExpressionKind.LAMBDA) return null;
                todo.push([pattern.body, expr.body, makeSymbolMap(symbolMaps, pattern.arg, expr.arg)]);
                break;
            }
            case ExpressionKind.FN_TYPE:
                if (typeof expr !== 'object' || expr.kind !== ExpressionKind.FN_TYPE) return null;
                todo.push(
                    [pattern.outputType, expr.outputType, makeSymbolMap(symbolMaps, pattern.arg, expr.arg)],
                    [pattern.inputType, expr.inputType, symbolMaps],
                );
                break;
            case ExpressionKind.TYPE_UNIVERSE:
                if (typeof expr !== 'object' || expr.kind !== ExpressionKind.TYPE_UNIVERSE) return null;
                todo.push([pattern.subscript, expr.subscript, symbolMaps]);
                break;
            case ExpressionKind.UNIVERSE_SUBSCRIPT_TYPE:
                if (typeof expr !== 'object' || expr.kind !== ExpressionKind.UNIVERSE_SUBSCRIPT_TYPE) return null;
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

export function evaluateFunction(context: SymbolRegistry, fn: Expression, arg: Expression) {

}

export const enum DiagnosticKind {
    NOT_A_TYPE,
    TYPE_MISSMATCH,
    UNTYPED_EXPRESSION,
    FUNCTION_TYPE_EXPECTED,
}

export type Diagnostic =
    | DiagnosticNotAType
    | DiagnosticTypeMissMatch
    | DiagnosticUntypedExpression
    | DiagnosticFunctionTypeExpected
;

export interface DiagnosticNotAType {
    readonly kind: DiagnosticKind.NOT_A_TYPE;
    readonly type: Expression;
}

export interface DiagnosticTypeMissMatch {
    readonly kind: DiagnosticKind.TYPE_MISSMATCH;
    readonly expected: Expression;
    readonly actual: Expression;
    readonly value: Expression;
}

export interface DiagnosticUntypedExpression {
    readonly kind: DiagnosticKind.UNTYPED_EXPRESSION;
    readonly expr: Expression;
}

export interface DiagnosticFunctionTypeExpected {
    readonly kind: DiagnosticKind.FUNCTION_TYPE_EXPECTED;
    readonly type: Expression;
}

export class Analyser {
    private readonly todo: ((self: Analyser, context: SymbolRegistry) => void)[] = [];
    private readonly stack: [Expression, Expression][] = [];
    private readonly diagnostics: Diagnostic[] = [];
    private readonly symbolEntryOverride: Map<Symbol, SymbolEntry[]> = new Map();
    private iterations = 0;
    private getSymbolEntry(context: SymbolRegistry, symbol: Symbol) {
        const r = this.symbolEntryOverride.get(symbol);
        if (r !== void 0) {
            assert(r.length > 0);
            return r[r.length - 1];
        } else return context.getSymbolEntry(symbol);
    }
    private enterScope(context: SymbolRegistry, symbol: Symbol) {
        if (!this.symbolEntryOverride.has(symbol)) {
            this.symbolEntryOverride.set(symbol, []);
        }
        const ret: SymbolEntry = {
            name: context.getSymbolEntry(symbol).name,
            parent: null,
            subSymbols: new Map(),
        };
        this.symbolEntryOverride.get(symbol)!.push(ret);
        return ret;
    }
    private leaveScope(symbol: Symbol) {
        const entry = this.symbolEntryOverride.get(symbol)!;
        entry.pop();
        if (entry.length === 0) {
            this.symbolEntryOverride.delete(symbol);
        }
    }
    private addInferedType(symbol: Symbol, type: Expression) {
        const r = this.symbolEntryOverride.get(symbol);
        if (r !== void 0) {
            assert(r.length > 0);
            const entry = r[r.length - 1];
            if (entry.info === void 0) {
                entry.info = {downValue: []};
            }
        }
    }
    combineTypes(type1: Expression | null, type2: Expression | null) {
        if (type1 !== null && type2 !== null) {
            this.todo.push((self, context) => {

            });
        }
    }
    expand(expr: Expression, typeHint: Expression | null) {
        this.todo.push((self, context) => {
            switch (expr.kind) {
                case ExpressionKind.SYMBOL: {
                    const entry = self.getSymbolEntry(context, expr.symbol);
                    const type = entry.info?.type;
                    if (type !== void 0) {
                        this.todo.push(self => {
                            const [type] = self.stack.pop()!;
                            if (entry.info?.ownValue !== void 0) {
                                self.expand(entry.info.ownValue, type);
                                self.iterations++;
                            } else {
                                self.stack.push([expr, type]);
                            }
                        });
                        this.expand(type, null);
                    } else {
                        if (typeHint !== null) {
                            this.addInferedType(expr.symbol, typeHint);
                        }
                        if (entry.info?.ownValue !== void 0) {
                            self.expand(entry.info.ownValue, typeHint);
                            self.iterations++;
                        } else {
                            self.diagnostics.push({kind: DiagnosticKind.UNTYPED_EXPRESSION, expr});
                        }
                    }
                    return;
                }
                case ExpressionKind.CALL: self._doCall(context, expr, typeHint);
                default: panic();
            }
        });
    }
    private _doCall(context: SymbolRegistry, expr: CallExpression, typeHint: Expression | null) {
        const arg = expr.args[0];
        const restArgs = expr.args.slice(1);
        this.todo.push((self, context) => {
            const [fn, fnType] = self.stack.pop()!;
            if (fnType.kind !== ExpressionKind.FN_TYPE) {
                self.diagnostics.push({
                    kind: DiagnosticKind.FUNCTION_TYPE_EXPECTED,
                    type: fnType,
                });
                return;
            }
            self.todo.push((self, context) => {
                const [arg, argType] = self.stack.pop()!;
                if (fnType.arg !== void 0) {
                    const entry = self.enterScope(context, fnType.arg);
                    entry.info = {ownValue: arg, downValue: []};
                    self.todo.push((self, context) => {
                        self.leaveScope(fnType.arg ?? panic());
                        self._doCall2(context, fn, arg, argType, self.stack.pop()![0], restArgs);
                    });
                    self.expand(fnType.outputType, null);
                } else {
                    self._doCall2(context, fn, arg, argType, fnType.outputType, restArgs);
                }
            });
            self.expand(arg, fnType.inputType);
        });
        this.expand(expr.fn, typeHint !== null ? {kind: ExpressionKind.FN_TYPE, inputType: {kind: ExpressionKind.PLACEHOLDER}, outputType: typeHint} : null);
    }
    private _doCall2(context: SymbolRegistry, fn: Expression, arg: Expression, argType: Expression, returnType: Expression, restArgs: Expression[]) {
        if (fn.kind === ExpressionKind.CALL) {
            fn = {kind: ExpressionKind.CALL, fn: fn.fn, args: fn.args.concat([arg])};
        }
        if (restArgs.length > 0) {
            this.todo.push((self, context) => {

            });
        }
        switch (fn.kind) {
            case ExpressionKind.LAMBDA: {
                const entry = this.enterScope(context, fn.arg);
                entry.info = {type: argType, ownValue: arg, downValue: []};
                this.expand(fn.body, returnType);
                break;
            }
        }
    }
    checkType(value: Expression, type: Expression) {
        this.todo.push((self, context) => {

        });
    }
    iterate(context: SymbolRegistry, maxIterations: number | null) {
        this.iterations = 0;
        while (this.todo.length > 0) {
            if (this.diagnostics.length > 0 || maxIterations !== null && this.iterations > maxIterations) return;
            const t = this.todo.pop()!;
            t(this, context);
        }
    }
}

export function replaceSymbols(expr: Expression, maps: Map<Symbol, Expression>) {

}

export function mapAll(context: SymbolRegistry, expr: Expression, replacer: (context: SymbolRegistry, expr: Expression) => Expression) {
    const stack: Expression[] = [];
    const todo: (Expression | ((stack: Expression[]) => void))[] = [expr];
    while (todo.length > 0) {

    }
}

export function inputForm(context: SymbolRegistry, expr: Expression) {
    const stack: string[] = [];
    const todo: (Expression | ((stack: string[]) => void))[] = [expr];
    while (todo.length > 0) {
        const t = todo.pop()!;
        if (typeof t === 'function') {
            t(stack);
        } else switch (t.kind) {
            case ExpressionKind.SYMBOL: stack.push(context.stringifySymbol(t.symbol)); break;
            case ExpressionKind.FN_TYPE: {
                const needsParenth = t.inputType.kind === ExpressionKind.FN_TYPE;
                const arg = t.arg;
                todo.push(stack => {
                    const outputType = stack.pop()!;
                    const inputType = stack.pop()!;
                    if (arg !== void 0) {
                        const name = context.getSymbolEntry(arg).name;
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
                    stack.push(`\\${context.getSymbolEntry(arg).name} ${body}`);
                }, t.body);
                break;
            }
            case ExpressionKind.PATTERN: {
                if (t.variable !== void 0) {
                    stack.push(`?${context.getSymbolEntry(t.variable).name}`);
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
            case ExpressionKind.TYPE_UNIVERSE: {
                todo.push(stack => {
                    stack.push(`type(${stack.pop()!})`);
                }, t.subscript);
                break;
            }
            case ExpressionKind.UNIVERSE_SUBSCRIPT_TYPE: stack.push('typen'); break;
            case ExpressionKind.UNIVERSE_SUBSCRIPT: stack.push(`${t.value.toString()}n`); break;
            default: panic();
        }
    }
    assert(stack.length === 1);
    return stack[0];
}
