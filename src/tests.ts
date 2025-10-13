import { SymbolRegistry } from "./expression";
import { analyse, FileId, parse } from "./parser";

function testParse(input: string) {
    const reg = new SymbolRegistry();
    reg.defineInternalSymbols();
    const [outerSymbol] = reg.addNewSymbol(null, "root");
    const ast = parse(input);
    if (!Array.isArray(ast)) {
        analyse(reg, outerSymbol, ast, 0 as FileId);
        for (const line of reg.dump()) {
            console.log(line);
        }
    }
}

testParse(`
Nat: typen
Nat.zero: Nat
Nat.succ: Nat -> Nat
Nat.ind: (n: typen) -> (C: type(n)) -> C(Nat.zero) -> ((x: Nat) -> C(x) -> C(Nat.succ(x))) -> (x: Nat) -> C(x)
`);
