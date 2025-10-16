import { Symbol, Expander, Expression, ExpressionKind, ExpressionLogger, ExpressionMessage, LEVEL_TYPE, symbolExpression, SymbolRegistry, TempSymbolRegistry, replaceOneSymbol, replaceSymbols, toPlainString, checkOwnValueCycle } from "./expression";
import { assert, complement, panic } from "./util";

export const enum DiagnosticKind {
    UNTYPED_EXPRESSION,
    UNEQUAL,
    UNMET_SUBSCRIPT_CONSTRAINT,
    UNRESOLVED_CONSTRAINT,
    UNINFERED_VAR,
    FN_TYPE_EXPECTED,
}

export type Diagnostic =
    | DiagnosticUntypedExpression
    | DiagnosticUnequal
    | DiagnosticUnmetUniverseSubscriptConstraint
    | DiagnosticUnresolvedConstraint
    | DiagnosticUninferedVar
    | DiagnosticFnTypeExpected
;

export interface DiagnosticUntypedExpression {
    readonly kind: DiagnosticKind.UNTYPED_EXPRESSION;
    readonly expr: Expression;
}

export interface DiagnosticUnequal {
    readonly kind: DiagnosticKind.UNEQUAL;
    readonly expr1: Expression;
    readonly expr2: Expression;
}

export interface DiagnosticUnmetUniverseSubscriptConstraint {
    readonly kind: DiagnosticKind.UNMET_SUBSCRIPT_CONSTRAINT;
    readonly smaller: number;
    readonly larger: number;
}

export interface DiagnosticUnresolvedConstraint {
    readonly kind: DiagnosticKind.UNRESOLVED_CONSTRAINT;
    readonly constraint: Constraint;
}

export interface DiagnosticUninferedVar {
    readonly kind: DiagnosticKind.UNINFERED_VAR;
    readonly symbols: Symbol[];
}

export interface DiagnosticFnTypeExpected {
    readonly kind: DiagnosticKind.FN_TYPE_EXPECTED;
    readonly type: Expression;
}

export function renderDiagnostic(diagnostic: Diagnostic): ExpressionMessage {
    switch (diagnostic.kind) {
        case DiagnosticKind.UNEQUAL: return ['uneqal expressions ', diagnostic.expr1, ' and ', diagnostic.expr2];
        case DiagnosticKind.UNINFERED_VAR: {
            const s: ExpressionMessage = [];
            for (const symbol of diagnostic.symbols) {
                s.push(symbolExpression(symbol, null), ', ');
            }
            return ['cannot infer all variables: ', ...s];
        }
        case DiagnosticKind.UNMET_SUBSCRIPT_CONSTRAINT: return [`unmet subscript constraint: ${diagnostic.smaller} < ${diagnostic.larger}`];
        case DiagnosticKind.UNRESOLVED_CONSTRAINT: return ['unresolved constraint: ', ...dumpConstraint(diagnostic.constraint)];
        case DiagnosticKind.UNTYPED_EXPRESSION: return ['untyped expression ', diagnostic.expr];
        case DiagnosticKind.FN_TYPE_EXPECTED: return ['function type expected: ', diagnostic.type];
    }
}

export const enum ConstraintKind {
    FN,
    TYPE,
    EQUAL,
    FN_TYPE_EQUAL,
}

export type Constraint =
    | NormalTypeConstraint
    | EqualConstraint
    | FnTypeConstraint
    | FnTypeEqualConstraint
    ;

export interface NormalTypeConstraint {
    readonly kind: ConstraintKind.TYPE;
    readonly expr: Expression;
    readonly type: Expression;
}

export interface FnTypeConstraint {
    readonly kind: ConstraintKind.FN;
    readonly expr: Expression;
    readonly args: Expression[];
    readonly outputType: Expression;
}

export type TypeConstraint = NormalTypeConstraint | FnTypeConstraint;

export interface EqualConstraint {
    readonly kind: ConstraintKind.EQUAL;
    readonly expr1: Expression;
    readonly expr2: Expression;
}

export interface FnTypeEqualConstraint {
    readonly kind: ConstraintKind.FN_TYPE_EQUAL;
    readonly fnType: Expression;
    readonly args: Expression[];
    readonly outputType: Expression;
}

export function dumpConstraint(con: Constraint): ExpressionMessage {
    switch (con.kind) {
        case ConstraintKind.TYPE: return [{kind: ExpressionKind.TYPE_ASSERTION, type: con.type, expr: con.expr}];
        case ConstraintKind.EQUAL: return [{kind: ExpressionKind.EQUAL, lhs: con.expr1, rhs: con.expr2}];
        case ConstraintKind.FN: return [{kind: ExpressionKind.TYPE_ASSERTION, expr: {kind: ExpressionKind.CALL, args: con.args, fn: con.expr}, type: con.outputType}];
        case ConstraintKind.FN_TYPE_EQUAL: return [{kind: ExpressionKind.TYPE_ASSERTION, expr: {kind: ExpressionKind.CALL, args: con.args, fn: con.fnType}, type: con.outputType}];
    }
}

export class ConstraintSolver {
    readonly registry: TempSymbolRegistry;
    private readonly diagnostics: Diagnostic[] = [];
    private readonly constraints: Constraint[] = [];
    private readonly unlockedSymbols: Set<Symbol> = new Set();
    private readonly affectedSymbols: Set<Symbol> = new Set();
    constructor(readonly context: SymbolRegistry, readonly logger: ExpressionLogger) {
        this.registry = new TempSymbolRegistry(context);
    }
    expand(expr: Expression) {
        const expander = new Expander(this.registry);
        return expander.expand(expr);
    }
    private trySetOwnValue(symbol: Symbol, value: Expression) {
        const entry = this.registry.getSymbolEntry(symbol);
        if (entry.ownValue !== void 0) return false;
        if (!this.registry.isTempSymbol(symbol)) return false;
        if (!checkOwnValueCycle(symbol, value)) {
            this.diagnostics.push({kind: DiagnosticKind.UNEQUAL, expr1: symbolExpression(symbol, null), expr2: value});
            return false;
        }
        entry.ownValue = value;
        if (entry.type !== void 0) {
            this.addTypeConstraint(value, entry.type);
        }
        if (!this.registry.isTempSymbol(symbol)) {
            this.affectedSymbols.add(symbol);
        }
        return true;
    }
    private matchLevelSucc(expr1: Expression, expr2: Expression) {
        if (expr2.kind === ExpressionKind.LEVEL_SUCC && expr1.kind !== ExpressionKind.LEVEL_SUCC) {
            const tmp = expr1;
            expr2 = expr1;
            expr1 = tmp;
        }
        if (expr1.kind === ExpressionKind.LEVEL_SUCC) {
            if (expr2.kind === ExpressionKind.LEVEL_SUCC) {
                this.addEqualConstraint(expr1.expr, expr2.expr);
                return true;
            } else if (expr2.kind === ExpressionKind.LEVEL) {
                if (expr2.value > 0) {
                    this.addEqualConstraint(expr1.expr, {kind: ExpressionKind.LEVEL, value: expr2.value - 1});
                } else {
                    this.diagnostics.push({kind: DiagnosticKind.UNEQUAL, expr1, expr2});
                }
                return true;
            }
        }
        return false;
    }
    private evaluateEqualConstraint(con: EqualConstraint, previouslyNoChange: boolean): boolean {
        let [expr1, changed1] = this.expand(con.expr1);
        let [expr2, changed2] = this.expand(con.expr2);
        if (expr1.kind !== ExpressionKind.SYMBOL && expr2.kind === ExpressionKind.SYMBOL) {
            const tmp = expr1;
            expr1 = expr2;
            expr2 = tmp;
        }
        if (expr1.kind === ExpressionKind.SYMBOL && expr2.kind === ExpressionKind.SYMBOL && !this.registry.isTempSymbol(expr1.symbol) && this.registry.isTempSymbol(expr2.symbol)) {
            const tmp = expr1;
            expr1 = expr2;
            expr2 = tmp;
        }
        if (expr1.kind === ExpressionKind.SYMBOL) {
            if (expr2.kind === ExpressionKind.SYMBOL && expr1.symbol === expr2.symbol) return true;
            if (this.trySetOwnValue(expr1.symbol, expr2)) return true;
        }
        if (expr1.kind === ExpressionKind.LAMBDA && expr2.kind === ExpressionKind.LAMBDA) {
            const arg1 = this.registry.createTempSymbol(true, null);
            const arg2 = this.registry.createTempSymbol(true, null);
            this.addEqualConstraint(
                replaceOneSymbol(expr1.body, expr1.arg, symbolExpression(arg1, null)),
                replaceOneSymbol(expr2.body, expr2.arg, symbolExpression(arg2, null)),
            );
            return true;
        }
        if (expr1.kind === ExpressionKind.FN_TYPE && expr2.kind === ExpressionKind.FN_TYPE) {
            this.addEqualConstraint(expr1.inputType, expr2.inputType);
            let output1 = expr1.outputType;
            let output2 = expr2.outputType;
            if (expr1.arg !== void 0) {
                const arg = symbolExpression(this.registry.createTempSymbol(true, expr1.inputType), null);
                output1 = replaceOneSymbol(output1, expr1.arg, arg);
            }
            if (expr2.arg !== void 0) {
                const arg = symbolExpression(this.registry.createTempSymbol(true, expr2.inputType), null);
                output2 = replaceOneSymbol(output2, expr2.arg, arg);
            }
            this.addEqualConstraint(output1, output2);
            return true;
        }
        if (expr1.kind === ExpressionKind.UNIVERSE && expr2.kind === ExpressionKind.UNIVERSE) {
            this.addEqualConstraint(expr1.subscript, expr2.subscript);
            return true;
        }
        if (expr1.kind === ExpressionKind.LEVEL_TYPE && expr2.kind === ExpressionKind.LEVEL_TYPE) {
            return true;
        }
        if (expr1.kind === ExpressionKind.LEVEL && expr2.kind === ExpressionKind.LEVEL) {
            if (expr1.value !== expr2.value) {
                this.diagnostics.push({kind: DiagnosticKind.UNEQUAL, expr1, expr2});
            }
            return true;
        }
        if (this.matchLevelSucc(expr1, expr2)) return true;

        if (previouslyNoChange && expr1.kind === ExpressionKind.CALL && expr2.kind === ExpressionKind.CALL) {
            if (expr1.args.length !== expr2.args.length) {
                this.diagnostics.push({kind: DiagnosticKind.UNEQUAL, expr1, expr2});
                return false;
            } else {
                this.addEqualConstraint(expr1.fn, expr2.fn);
                for (let i = 0, a = expr1.args, b = expr2.args; i < a.length; i++) {
                    this.addEqualConstraint(a[i], b[i]);
                }
                return true;
            }
        }

        if (changed1 || changed2) {
            this.addEqualConstraint(expr1, expr2);
        } else {
            this.constraints.push(con);
        }
        return changed1 || changed2;
    }
    private evaluateTypeConstraint(con: TypeConstraint): boolean {
        const expr = con.expr;
        switch (expr.kind) {
            case ExpressionKind.SYMBOL: {
                const entry = this.registry.getSymbolEntry(expr.symbol);
                const symbolType = entry.type;
                if (symbolType !== void 0) {
                    switch (con.kind) {
                        case ConstraintKind.TYPE: this.addEqualConstraint(symbolType, con.type); break;
                        case ConstraintKind.FN: this.addFnTypeEqualConstraint(symbolType, con.args, con.outputType); break;
                        default: panic();
                    }
                } else if (this.registry.isTempSymbol(expr.symbol) || this.unlockedSymbols.has(expr.symbol)) {
                    this.affectedSymbols.add(expr.symbol);
                    if (con.kind === ConstraintKind.TYPE) {
                        entry.type = con.type;
                    } else {
                        entry.type = this.makeInferedFnType(con.args, con.outputType);
                    }
                    if (entry.ownValue !== void 0) {
                        this.addTypeConstraint(entry.ownValue, entry.type);
                    }
                } else {
                    this.diagnostics.push({
                        kind: DiagnosticKind.UNTYPED_EXPRESSION,
                        expr,
                    });
                }
                return true;
            }
            case ExpressionKind.CALL: {
                if (con.kind === ConstraintKind.TYPE) {
                    this.addFnTypeConstraint(expr.fn, expr.args, con.type);
                } else {
                    this.addFnTypeConstraint(expr.fn, con.args.concat(expr.args), con.outputType);
                }
                return true;
            }
            case ExpressionKind.LAMBDA: {
                if (con.kind === ConstraintKind.TYPE) {
                    const inputType = symbolExpression(this.registry.createTempSymbol(false, null), null);
                    const outputType = symbolExpression(this.registry.createTempSymbol(false, null), null);
                    const arg = this.registry.createTempSymbol(true, inputType);
                    this.addTypeTypeConstraint(inputType);
                    this.addTypeTypeConstraint(outputType);
                    this.addTypeConstraint(replaceOneSymbol(expr.body, expr.arg, symbolExpression(arg, null)), outputType);
                    this.addEqualConstraint({kind: ExpressionKind.FN_TYPE, arg, inputType, outputType}, con.type);
                } else if (con.args.length === 1) {
                    this.addTypeConstraint(replaceOneSymbol(expr.body, expr.arg, con.args[0]), con.outputType);
                } else {
                    this.addFnTypeConstraint(replaceOneSymbol(expr.body, expr.arg, con.args[0]), con.args.slice(1), con.outputType);
                }
                return true;
            }
            case ExpressionKind.FN_TYPE: {
                const inputTypeLevel = symbolExpression(this.registry.createTempSymbol(false, LEVEL_TYPE), null);
                const outputTypeLevel = symbolExpression(this.registry.createTempSymbol(false, LEVEL_TYPE), null);
                this.addTypeConstraint(expr.inputType, {kind: ExpressionKind.UNIVERSE, subscript: inputTypeLevel});
                let outputType = expr.outputType;
                if (expr.arg !== void 0) {
                    const arg = this.registry.createTempSymbol(true, expr.inputType);
                    outputType = replaceOneSymbol(outputType, expr.arg, symbolExpression(arg, null));
                }
                this.addTypeConstraint(outputType, {kind: ExpressionKind.UNIVERSE, subscript: outputTypeLevel});
                const type: Expression = {kind: ExpressionKind.UNIVERSE, subscript: {kind: ExpressionKind.LEVEL_MAX, lhs: inputTypeLevel, rhs: outputTypeLevel}};
                if (con.kind === ConstraintKind.TYPE) {
                    this.addEqualConstraint(con.type, type);
                } else {
                    this.diagnostics.push({kind: DiagnosticKind.FN_TYPE_EXPECTED, type});
                }
                return true;
            }
            case ExpressionKind.PLACEHOLDER: return true;
            case ExpressionKind.UNIVERSE: {
                const type: Expression = {kind: ExpressionKind.UNIVERSE, subscript: {kind: ExpressionKind.LEVEL_SUCC, expr: expr.subscript}};
                if (con.kind === ConstraintKind.TYPE) {
                    this.addEqualConstraint(type, con.type);
                } else {
                    this.diagnostics.push({kind: DiagnosticKind.FN_TYPE_EXPECTED, type});
                }
                return true;
            }
            case ExpressionKind.LEVEL:
            case ExpressionKind.LEVEL_SUCC:
            case ExpressionKind.LEVEL_MAX:
                if (con.kind === ConstraintKind.TYPE) {
                    this.addEqualConstraint(con.type, LEVEL_TYPE);
                } else {
                    this.diagnostics.push({kind: DiagnosticKind.FN_TYPE_EXPECTED, type: LEVEL_TYPE});
                }
                return true;
            case ExpressionKind.LEVEL_TYPE: {
                const type: Expression = {kind: ExpressionKind.UNIVERSE, subscript: {kind: ExpressionKind.LEVEL, value: 0}};
                if (con.kind === ConstraintKind.TYPE) {
                    this.addEqualConstraint(type, con.type);
                } else {
                    this.diagnostics.push({kind: DiagnosticKind.FN_TYPE_EXPECTED, type});
                }
                return true;
            }
            default: panic();
        }
    }
    private makeInferedFnType(args: Expression[], outputType: Expression) {
        let ret = outputType;
        for (let i = 0; i < args.length; i++) {
            const arg = args[args.length - 1 - i];
            const sub = symbolExpression(this.registry.createTempSymbol(false, null), null);
            const inputType = symbolExpression(this.registry.createTempSymbol(false, {kind: ExpressionKind.UNIVERSE, subscript: sub}), null);
            this.addTypeConstraint(arg, inputType);
            ret = {kind: ExpressionKind.FN_TYPE, inputType, outputType: ret };
        }
        return ret;
    }
    private evaluateFnTypeEqualConstraint(con: FnTypeEqualConstraint) {
        const [fn, changed] = this.expand(con.fnType);
        if (fn.kind === ExpressionKind.FN_TYPE) {
            this.addTypeConstraint(con.args[0], fn.inputType);
            let outputType = fn.outputType;
            if (fn.arg !== void 0) {
                outputType = replaceOneSymbol(outputType, fn.arg, con.args[0]);
            }
            if (con.args.length === 1) {
                this.addEqualConstraint(con.outputType, outputType);
            } else {
                this.addFnTypeEqualConstraint(outputType, con.args.slice(1), con.outputType);
            }
            return true;
        }
        if (changed) {
            this.addFnTypeEqualConstraint(con.fnType, con.args, con.outputType);
        } else {
            this.constraints.push(con);
        }
        return changed;
    }
    private evaluateConstraint(con: Constraint, previouslyNoChange: boolean) {
        switch (con.kind) {
            case ConstraintKind.FN:
            case ConstraintKind.TYPE: return this.evaluateTypeConstraint(con);
            case ConstraintKind.EQUAL: return this.evaluateEqualConstraint(con, previouslyNoChange);
            case ConstraintKind.FN_TYPE_EQUAL: return this.evaluateFnTypeEqualConstraint(con);
            default: panic();
        }
    }
    private finalCheck() {
        this.registry.forEachTempSymbol((s, entry) => {
            if (entry.type !== void 0 && entry.type.kind === ExpressionKind.LEVEL_TYPE && entry.ownValue === void 0) {
                entry.ownValue = {kind: ExpressionKind.LEVEL, value: 0};
            }
        });
        for (const con of this.constraints) {
            this.diagnostics.push({kind: DiagnosticKind.UNRESOLVED_CONSTRAINT, constraint: con});
        }
        const tempReps = new Map<Symbol, Expression>();
        let hasUninferedVar = false;
        const uninferedVars: Symbol[] = [];
        this.registry.forEachTempSymbol((s, entry) => {
            const ownValue = entry.ownValue;
            if (ownValue !== void 0) {
                tempReps.set(s, this.expand(ownValue)[0]);
            } else if (!entry.isLocal) {
                uninferedVars.push(s);
            }
        });
        if (uninferedVars.length > 0) {
            this.diagnostics.push({kind: DiagnosticKind.UNINFERED_VAR, symbols: uninferedVars});
        }
        this.affectedSymbols.forEach(s => {
            const entry = this.registry.getSymbolEntry(s);
            if (entry.type !== void 0) {
                entry.type = replaceSymbols(entry.type, tempReps);
            }
            if (entry.ownValue !== void 0) {
                entry.ownValue = replaceSymbols(entry.ownValue, tempReps);
            }
            if (entry.downValue !== void 0) {
                for (let i = 0, a = entry.downValue; i < a.length; i++) {
                    const v = a[i];
                    const reps = complement(tempReps, v.patterns);
                    a[i] = {lhs: replaceSymbols(v.lhs, reps), rhs: replaceSymbols(v.rhs, reps), patterns: v.patterns};
                }
            }
        });
    }
    private logDump(iterations: number) {
        this.logger.info(this.registry.parent, () => [`iteration ${iterations++}`]);
        for (const line of this.dump()) {
            this.logger.info(this.registry.parent, () => line);
        }
    }
    private iterate(previouslyNoChange: boolean) {
        let changed = false;
        const constraints = this.constraints.slice(0);
        this.constraints.length = 0;
        for (const con of constraints) {
            if (this.evaluateConstraint(con, previouslyNoChange)) {
                changed = true;
            }
        }
        return changed;
    }
    run(maxIterations: number) {
        this.diagnostics.length = 0;
        const date = new Date();
        let done = false;
        let iterations = 0;
        while (!done) {
            this.logDump(iterations);
            if (iterations > maxIterations) {
                break;
            }
            done = !this.iterate(false);
            if (done) {
                done = !this.iterate(true);
            }
        }
        this.logDump(iterations);
        const elapsed = new Date().valueOf() - date.valueOf();
        this.logger.info(this.registry.parent, () => [`took ${elapsed}ms`]);
        this.finalCheck();
        return this.diagnostics.slice(0);
    }
    dump() {
        const ret: ExpressionMessage[] = [];
        ret.push(['symbols:']);
        this.registry.forEachTempSymbol((s, entry) => {
            if (entry.type !== void 0) {
                ret.push(['    ', {kind: ExpressionKind.TYPE_ASSERTION, type: entry.type, expr: symbolExpression(s, null)}]);
            }
            if (entry.ownValue !== void 0) {
                ret.push(['    ', {kind: ExpressionKind.EQUAL, lhs: symbolExpression(s, null), rhs: entry.ownValue}]);
            }
        });
        ret.push(['constraints:']);
        for (const con of this.constraints) {
            ret.push(['    ', ...dumpConstraint(con)]);
        }
        ret.push(['end'])
        return ret;
    }
    unlockSymbol(s: Symbol) {
        this.unlockedSymbols.add(s);
    }
    addTypeTypeConstraint(type: Expression) {
        const sub = this.registry.createTempSymbol(false, LEVEL_TYPE);
        this.addTypeConstraint(type, {kind: ExpressionKind.UNIVERSE, subscript: symbolExpression(sub, null)});
    }
    createTypeSymbol(isLocal: boolean) {
        const level = this.registry.createTempSymbol(false, LEVEL_TYPE);
        return this.registry.createTempSymbol(isLocal, {kind: ExpressionKind.UNIVERSE, subscript: symbolExpression(level, null)});
    }
    addTypeConstraint(expr: Expression, type: Expression) {
        this.constraints.push({kind: ConstraintKind.TYPE, expr, type});
    }
    addEqualConstraint(smallerType: Expression, largerType: Expression) {
        this.constraints.push({kind: ConstraintKind.EQUAL, expr1: smallerType, expr2: largerType});
    }
    addFnTypeConstraint(expr: Expression, args: Expression[], outputType: Expression) {
        this.constraints.push({kind: ConstraintKind.FN, expr, args, outputType});
    }
    addFnTypeEqualConstraint(fnType: Expression, args: Expression[], outputType: Expression) {
        this.constraints.push({kind: ConstraintKind.FN_TYPE_EQUAL, fnType, args, outputType});
    }
}
