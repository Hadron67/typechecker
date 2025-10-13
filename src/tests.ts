import { SymbolRegistry } from "./expression";
import { analyse, FileId, parse } from "./parser";

function testParse(input: string) {
    const reg = new SymbolRegistry();
    reg.defineInternalSymbols();
    const [outerSymbol] = reg.addNewSymbol(null, "root", false);
    const ast = parse(input);
    if (!Array.isArray(ast)) {
        analyse(reg, outerSymbol, ast, 0 as FileId);
        for (const line of reg.dump()) {
            console.log(line);
        }
    }
}

testParse(`
Nat: type(0n)
Nat.zero: Nat
Nat.succ: Nat -> Nat
Nat.ind: (n: typen) -> (C: type(n)) -> C(Nat.zero) -> ((x: Nat) -> C(x) -> C(Nat.succ(x))) -> (x: Nat) -> C(x)
Nat.ind(?, ?, ?c0, ?cs, Nat.zero) := c0
Nat.ind(?n, ?C, ?c0, ?cs, Nat.succ(?x)) := cs(x, Nat.ind(n, C, c0, cs, x))

Bool: type(0n)
Bool.true: Bool
Bool.false: Bool
Bool.ind: (n: typen) -> (C: type(n)) -> C(Bool.true) -> C(Bool.false) -> (x: Bool) -> C(x)
Bool.ind(?, ?, ?ctrue, ?cfalse, Bool.true) := ctrue
Bool.ind(?, ?, ?ctrue, ?cfalse, Bool.false) := cfalse
`);
