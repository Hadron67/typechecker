import { ConsoleLogger, SymbolRegistry, toPlainString } from "./expression";
import { analyse, FileId, parse, ParseDiagnostic } from "./parser";
import { Diagnostic, renderDiagnostic } from "./solver";
import { panic } from "./util";

function doTest(reg: SymbolRegistry, input: string, silence: boolean): [ParseDiagnostic[], Diagnostic[]] {
    reg.defineInternalSymbols();
    const [outerSymbol] = reg.addNewSymbol(null, "root", false);
    const ast = parse(input);
    if (!Array.isArray(ast)) {
        const logger = new ConsoleLogger();
        if (silence) logger.enabled = false;
        const [parseDiagnostics, diagnostics] = analyse(reg, outerSymbol, ast, 0 as FileId, 10000000, logger);
        if (!silence) {
            for (const line of reg.dump()) {
                console.log(line);
            }
        }
        return [parseDiagnostics, diagnostics];
    } else return [ast, []];
}

function testOk(input: string, silence: boolean) {
    const reg = new SymbolRegistry();
    reg.defineInternalSymbols();
    const [parseDiagnostics, diagnostics] = doTest(reg, input, silence);
    if (parseDiagnostics.length > 0) {
        for (const d of parseDiagnostics) {
            console.log(d.msg);
        }
        panic();
    }
    if (diagnostics.length > 0) {
        for (const d of diagnostics) {
            console.log(toPlainString(reg, renderDiagnostic(d)));
        }
        panic();
    }
}

testOk(`
Nat.zero: Nat
Nat.succ: Nat -> Nat
Nat.ind: (n: builtin.Level) -> (C: Nat -> type(n)) -> C(Nat.zero) -> ((x: Nat) -> C(x) -> C(Nat.succ(x))) -> (x: Nat) -> C(x)
Nat.ind(?n, ?C, ?c0, ?cs, Nat.zero) := c0
Nat.ind(?n, ?C, ?c0, ?cs, Nat.succ(?x)) := cs(x, Nat.ind(n, C, c0, cs, x))

Nat.double: Nat -> Nat = Nat.ind(0l, \\x Nat, Nat.zero, \\x\\y Nat.succ(Nat.succ(y)))
Nat.double(Nat.zero) :=== Nat.zero
Nat.double(Nat.succ(Nat.zero)) :=== Nat.succ(Nat.succ(Nat.zero))
Nat.double(Nat.succ(Nat.succ(Nat.zero))) :=== Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))
`, false);
