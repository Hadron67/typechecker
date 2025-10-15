import { Symbol, Expander, Expression, ExpressionKind, ExpressionLogger, ExpressionMessage, LEVEL_TYPE, symbolExpression, SymbolRegistry, TempSymbolRegistry, replaceOneSymbol, replaceSymbols, toPlainString } from "./expression";
import { assert, panic } from "./util";

export const enum DiagnosticKind {
    UNTYPED_EXPRESSION,
    UNEQUAL,
    UNMET_SUBSCRIPT_CONSTRAINT,
    UNRESOLVED_CONSTRAINT,
    UNINFERED_VAR,
}

export type Diagnostic =
    | DiagnosticUntypedExpression
    | DiagnosticUnequal
    | DiagnosticUnmetUniverseSubscriptConstraint
    | DiagnosticUnresolvedConstraint
    | DiagnosticUninferedVar
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
}

export function renderDiagnostic(diagnostic: Diagnostic): ExpressionMessage {
    switch (diagnostic.kind) {
        case DiagnosticKind.UNEQUAL: return ['uneqal expressions ', diagnostic.expr1, ' and ', diagnostic.expr2];
        case DiagnosticKind.UNINFERED_VAR: return ['cannot infer all variables'];
        case DiagnosticKind.UNMET_SUBSCRIPT_CONSTRAINT: return [`unmet subscript constraint: ${diagnostic.smaller} < ${diagnostic.larger}`];
        case DiagnosticKind.UNRESOLVED_CONSTRAINT: return ['unresolved constraint: ', ...dumpConstraint(diagnostic.constraint)];
        case DiagnosticKind.UNTYPED_EXPRESSION: return ['untyped expression ', diagnostic.expr];
    }
}

export const enum ConstraintKind {
    TYPE,
    EQUAL,
    SUBSCRIPT,
}

export type Constraint =
    | TypeConstraint
    | EqualConstraint
    | UniverseSubscriptConstraint
    ;

export interface TypeConstraint {
    readonly kind: ConstraintKind.TYPE;
    readonly expr: Expression;
    readonly type: Expression;
}

export interface EqualConstraint {
    readonly kind: ConstraintKind.EQUAL;
    readonly smallerType: Expression;
    readonly largerType: Expression;
}

export interface UniverseSubscriptConstraint {
    readonly kind: ConstraintKind.SUBSCRIPT;
    readonly smaller: Expression;
    readonly larger: Expression;
    readonly allowEqual: boolean;
}

export function dumpConstraint(con: Constraint): ExpressionMessage {
    switch (con.kind) {
        case ConstraintKind.TYPE: return [{kind: ExpressionKind.TYPE_ASSERTION, type: con.type, expr: con.expr}];
        case ConstraintKind.EQUAL: return [{kind: ExpressionKind.EQUAL, lhs: con.smallerType, rhs: con.largerType}];
        case ConstraintKind.SUBSCRIPT: return [{kind: ExpressionKind.LESS_THAN, lhs: con.smaller, rhs: con.larger}];
    }
}

type ConstraintSolverAction = (self: ConstraintSolver) => void;

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
    private setOwnValue(symbol: Symbol, value: Expression) {
        const entry = this.registry.getSymbolEntry(symbol);
        assert(entry.ownValue === void 0);
        entry.ownValue = value;
        this.affectedSymbols.add(symbol);
    }
    private canSetOwnValue(symbol: Symbol) {
        const entry = this.registry.getSymbolEntry(symbol);
        if (entry.ownValue !== void 0) return false;
        return this.registry.isTempSymbol(symbol) || this.unlockedSymbols.has(symbol);
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
    private evaluateEqualConstraint(expr1: Expression, expr2: Expression): boolean {
        if (expr1.kind === ExpressionKind.SYMBOL) {
            if (expr2.kind === ExpressionKind.SYMBOL) {
                if (expr1.symbol === expr2.symbol) return true;
                if (this.canSetOwnValue(expr1.symbol)) {
                    this.setOwnValue(expr1.symbol, expr2);
                    return true;
                }
                if (this.canSetOwnValue(expr2.symbol)) {
                    this.setOwnValue(expr2.symbol, expr1);
                    return true;
                }
            } else if (this.canSetOwnValue(expr1.symbol)) {
                this.setOwnValue(expr1.symbol, expr2);
                return true;
            }
        }
        if (expr2.kind === ExpressionKind.SYMBOL) {
            if (this.canSetOwnValue(expr2.symbol)) {
                this.setOwnValue(expr2.symbol, expr1);
                return true;
            }
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
        this.addEqualConstraint(expr1, expr2);
        return false;
    }
    private evaluateTypeUniverseSubscriptConstraint(smaller: Expression, larger: Expression, allowEqual: boolean): boolean {
        const [smaller2, changed1] = this.expand(smaller);
        const [larger2, changed2] = this.expand(larger);
        const changed = changed1 || changed2;
        smaller = smaller2;
        larger = larger2;
        if (smaller.kind === ExpressionKind.LEVEL && larger.kind === ExpressionKind.LEVEL) {
            if (smaller.value >= larger.value) {
                this.diagnostics.push({kind: DiagnosticKind.UNMET_SUBSCRIPT_CONSTRAINT, larger: smaller.value, smaller: smaller.value});
            }
            return true;
        }
        this.addTypeUniverseSubscriptConstraint(smaller, larger, allowEqual);
        return changed;
    }
    private solveUniverseSubcriptConstraints(cons: UniverseSubscriptConstraint[]) {
        const values = new Map<Symbol, number>();
        let done = false;
        while (!done) {
            done = true;
            for (const con of cons) {
                const {smaller, larger, allowEqual} = con;
                let smallerValue: number;
                if (smaller.kind === ExpressionKind.LEVEL) {
                    smallerValue = smaller.value;
                } else if (smaller.kind === ExpressionKind.SYMBOL) {
                    if (values.has(smaller.symbol)) {
                        smallerValue = values.get(smaller.symbol)!;
                    } else {
                        smallerValue = 0;
                        values.set(smaller.symbol, 0);
                        done = false;
                    }
                } else {
                    this.diagnostics.push({kind: DiagnosticKind.UNRESOLVED_CONSTRAINT, constraint: con});
                    return;
                }
                if (larger.kind === ExpressionKind.SYMBOL) {
                    const old = values.get(larger.symbol) ?? 0;
                    if (allowEqual ? old < smallerValue : old <= smallerValue) {
                        values.set(larger.symbol, allowEqual ? smallerValue : smallerValue + 1);
                        done = false;
                    }
                } else if (larger.kind === ExpressionKind.LEVEL && (allowEqual ? larger.value < smallerValue : larger.value <= smallerValue)) {
                    this.diagnostics.push({kind: DiagnosticKind.UNMET_SUBSCRIPT_CONSTRAINT, larger: larger.value, smaller: smallerValue});
                    return;
                }
            }
        }
        values.forEach((v, k) => {
            assert(this.canSetOwnValue(k));
            this.setOwnValue(k, {kind: ExpressionKind.LEVEL, value: v});
        });
        this.registry.forEachTempSymbol((s, entry) => {
            if (entry.type !== void 0 && entry.type.kind === ExpressionKind.LEVEL_TYPE && entry.ownValue === void 0) {
                entry.ownValue = {kind: ExpressionKind.LEVEL, value: 0};
            }
        });
    }
    private evaluateTypeConstraint(expr: Expression, type: Expression): boolean {
        switch (expr.kind) {
            case ExpressionKind.SYMBOL: {
                const entry = this.registry.getSymbolEntry(expr.symbol);
                const symbolType = entry.type;
                if (symbolType !== void 0) {
                    this.addEqualConstraint(symbolType, type);
                } else if (this.registry.isTempSymbol(expr.symbol) || this.unlockedSymbols.has(expr.symbol)) {
                    this.affectedSymbols.add(expr.symbol);
                    entry.type = type;
                } else {
                    this.diagnostics.push({
                        kind: DiagnosticKind.UNTYPED_EXPRESSION,
                        expr,
                    });
                }
                return true;
            }
            case ExpressionKind.CALL: {
                const inputType = symbolExpression(this.registry.createTempSymbol(false, null), null);
                this.addTypeTypeConstraint(inputType);
                const argSymbol = this.registry.createTempSymbol(true, null);
                const fn: Expression = expr.args.length === 1 ? expr.fn : {kind: ExpressionKind.CALL, fn: expr.fn, args: expr.args.slice(-1)};
                this.addTypeConstraint(fn, {kind: ExpressionKind.FN_TYPE, arg: argSymbol, inputType, outputType: type});
                this.addTypeConstraint(expr.args[expr.args.length - 1], inputType);
                return true;
            }
            case ExpressionKind.LAMBDA: {
                const inputType = symbolExpression(this.registry.createTempSymbol(false, null), null);
                const outputType = symbolExpression(this.registry.createTempSymbol(false, null), null);
                const arg = this.registry.createTempSymbol(true, inputType);
                this.addTypeTypeConstraint(inputType);
                this.addTypeTypeConstraint(outputType);
                this.addTypeConstraint(symbolExpression(arg, null), inputType);
                this.addTypeConstraint(replaceOneSymbol(expr.body, expr.arg, symbolExpression(arg, null)), outputType);
                this.addEqualConstraint({kind: ExpressionKind.FN_TYPE, arg, inputType, outputType}, type);
                return true;
            }
            case ExpressionKind.FN_TYPE: {
                
                return true;
            }
            case ExpressionKind.PLACEHOLDER: return true;
            case ExpressionKind.UNIVERSE: {
                const sub = this.registry.createTempSymbol(false, LEVEL_TYPE);
                this.addEqualConstraint({kind: ExpressionKind.UNIVERSE, subscript: {kind: ExpressionKind.LEVEL_SUCC, expr: symbolExpression(sub, null)}}, type);
                return true;
            }
            case ExpressionKind.LEVEL:
                this.addEqualConstraint(type, LEVEL_TYPE);
                return true;
            default: panic();
        }
    }
    private evaluateConstraint(con: Constraint) {
        switch (con.kind) {
            case ConstraintKind.TYPE: {
                return this.evaluateTypeConstraint(con.expr, con.type);
            }
            case ConstraintKind.EQUAL: {
                const [expr1, changed1] = this.expand(con.largerType);
                const [expr2, changed2] = this.expand(con.smallerType);
                return this.evaluateEqualConstraint(expr1, expr2) || changed1 || changed2;
            }
            case ConstraintKind.SUBSCRIPT: return this.evaluateTypeUniverseSubscriptConstraint(con.smaller, con.larger, con.allowEqual);
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
        this.registry.forEachTempSymbol((s, entry) => {
            const ownValue = entry.ownValue;
            if (ownValue !== void 0) {
                tempReps.set(s, this.expand(ownValue)[0]);
            } else if (!entry.isLocal) {
                hasUninferedVar = true;
            }
        });
        if (hasUninferedVar) {
            this.diagnostics.push({kind: DiagnosticKind.UNINFERED_VAR});
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
                    v[1] = replaceSymbols(v[1], tempReps);
                }
            }
        });
    }
    private iterate(maxIterations: number) {
        let done = false;
        let iterations = 0;
        while (!done) {
            if (iterations > maxIterations) {
                break;
            }
            done = true;
            this.logger.info(this.registry.parent, () => [`iteration ${iterations++}`]);
            for (const line of this.dump()) {
                this.logger.info(this.registry.parent, () => line);
            }
            const constraints = this.constraints.slice(0);
            this.constraints.length = 0;
            for (const con of constraints) {
                if (this.evaluateConstraint(con)) {
                    done = false;
                }
            }
        }
        this.logger.info(this.registry.parent, () => [`final state:`]);
        for (const line of this.dump()) {
            this.logger.info(this.registry.parent, () => line);
        }
        const constraints = this.constraints.slice(0);
        this.constraints.length = 0;
        const subscriptConstraints: UniverseSubscriptConstraint[] = [];
        for (const con of constraints) {
            if (con.kind === ConstraintKind.SUBSCRIPT) {
                subscriptConstraints.push(con);
            } else {
                this.constraints.push(con);
            }
        }
        // this.solveUniverseSubcriptConstraints(subscriptConstraints);
        this.finalCheck();
    }
    dump() {
        const ret: ExpressionMessage[] = [];
        this.registry.forEachTempSymbol((s, entry) => {
            if (entry.type !== void 0) {
                ret.push([{kind: ExpressionKind.TYPE_ASSERTION, type: entry.type, expr: symbolExpression(s, null)}]);
            }
            if (entry.ownValue !== void 0) {
                ret.push([{kind: ExpressionKind.EQUAL, lhs: symbolExpression(s, null), rhs: entry.ownValue}]);
            }
        });
        for (const con of this.constraints) {
            ret.push(dumpConstraint(con));
        }
        return ret;
    }
    unlockSymbol(s: Symbol) {
        this.unlockedSymbols.add(s);
    }
    addTypeTypeConstraint(type: Expression) {
        const sub = this.registry.createTempSymbol(false, LEVEL_TYPE);
        this.addTypeConstraint(type, {kind: ExpressionKind.UNIVERSE, subscript: symbolExpression(sub, null)});
    }
    addTypeConstraint(expr: Expression, type: Expression) {
        this.constraints.push({kind: ConstraintKind.TYPE, expr, type});
    }
    addEqualConstraint(smallerType: Expression, largerType: Expression) {
        this.constraints.push({kind: ConstraintKind.EQUAL, smallerType, largerType});
    }
    addTypeUniverseSubscriptConstraint(smaller: Expression, larger: Expression, allowEqual: boolean) {
        this.constraints.push({kind: ConstraintKind.SUBSCRIPT, smaller, larger, allowEqual});
    }
    run() {
        this.diagnostics.length = 0;
        this.iterate(100000);
        return this.diagnostics.slice(0);
    }
}
