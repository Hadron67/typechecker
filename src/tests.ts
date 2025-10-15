import { SymbolRegistry, toPlainString } from "./expression";
import { analyse, FileId, parse } from "./parser";
import { renderDiagnostic } from "./solver";

function testParse(input: string) {
    const reg = new SymbolRegistry();
    reg.defineInternalSymbols();
    const [outerSymbol] = reg.addNewSymbol(null, "root", false);
    const ast = parse(input);
    if (!Array.isArray(ast)) {
        const [parseDiagnostics, diagnostics] = analyse(reg, outerSymbol, ast, 0 as FileId);
        if (parseDiagnostics.length > 0) {
            for (const d of parseDiagnostics) {
                console.log(d.msg);
            }
        }
        if (diagnostics.length > 0) {
            for (const d of diagnostics) {
                console.log(toPlainString(reg, renderDiagnostic(d)));
            }
        }
        for (const line of reg.dump()) {
            console.log(line);
        }
    }
}

testParse(`
Nat.zero: Nat
`);
