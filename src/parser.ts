import { Expression, ExpressionKind, SymbolRegistry, Symbol, ConsoleLogger, symbolExpression, replaceSymbols, ExpressionLogger } from "./expression";
import { ConstraintSolver, Diagnostic } from "./solver";
import { assert, panic, popReversed, pushReversed } from "./util";

const CCODE_A = 'A'.charCodeAt(0);
const CCODE_Z = 'Z'.charCodeAt(0);
const CCODE_LOWER_A = 'a'.charCodeAt(0);
const CCODE_LOWER_Z = 'z'.charCodeAt(0);

const CCODE_0 = '0'.charCodeAt(0);
const CCODE_9 = '9'.charCodeAt(0);
const CCODE_OPEN_PARENTH = '('.charCodeAt(0);
const CCODE_CLOSE_PARENTH = ')'.charCodeAt(0);
const CCODE_OPEN_BRACKET = '['.charCodeAt(0);
const CCODE_CLOSE_BRACKET = ']'.charCodeAt(0);
const CCODE_DASH = '-'.charCodeAt(0);
const CCODE_GT = '>'.charCodeAt(0);
const CCODE_BSLASH = '\\'.charCodeAt(0);
const CCODE_DOT = '.'.charCodeAt(0);
const CCODE_EQUAL = '='.charCodeAt(0);
const CCODE_COLON = ':'.charCodeAt(0);
const CCODE_COMMA = ','.charCodeAt(0);
const CCODE_EAR = '?'.charCodeAt(0);
const CCODE_N = 'n'.charCodeAt(0);
const CCODE_L = 'l'.charCodeAt(0);
const CCODE_SEMI_COLON = ';'.charCodeAt(0);

const CCODE_SPACE = ' '.charCodeAt(0);
const CCODE_CR = '\r'.charCodeAt(0);
const CCODE_LF = '\n'.charCodeAt(0);
const CCODE_TAB = '\t'.charCodeAt(0);

export const enum TokenKind {
    EOF,
    NUMBER,
    IDENTIFIER,
    COLON,
    DOT,
    OPEN_PARENTH,
    CLOSE_PARENTH,
    OPEN_BRACKET,
    CLOSE_BRACKET,
    OPEN_BRACE,
    CLOSE_BRACE,
    COMMA,
    IMPORT,
    TYPE,
    ARROW,
    BSLASH,
    ASSIGN,
    OPERATOR,
    PROD,
    EAR,
    EQUIV,
    SEMI_COLON,
}

const KEYWORKDS: {[name: string]: TokenKind} = {
    'prod': TokenKind.PROD,
    'import': TokenKind.IMPORT,
    'type': TokenKind.TYPE,
};

export interface SourceRange {
    readonly start: number;
    readonly length: number;
}

export const UNKNOWN_SOURCERANGE: SourceRange = {start: 0, length: 0};

export interface Token extends SourceRange {
    readonly kind: TokenKind;
    readonly text: string;
    readonly value?: number;
}

export interface SourceLocation {
    readonly line: number;
    readonly column: number;
}

export function positionToSourceLocation(source: string, position: number) {
    let line = 0;
    let column = 0;
    for (let i = 0; i < position && i < source.length; i++) {
        const ch = source.charCodeAt(i);
        if (ch === CCODE_LF) {
            line++;
            column = 0;
        } else {
            column++;
        }
    }
}

function isWhitespace(ch: number) {
    return ch === CCODE_CR || ch === CCODE_LF || ch === CCODE_SPACE || ch === CCODE_TAB;
}

function isIdentifierPart(ch: number) {
    return ch >= CCODE_A && ch <= CCODE_Z || ch >= CCODE_LOWER_A && ch <= CCODE_LOWER_Z || ch >= CCODE_0 && ch <= CCODE_9;
}

function isDigit(ch: number) {
    return ch >= CCODE_0 && ch <= CCODE_9;
}

export interface ParseDiagnostic extends SourceRange {
    readonly msg: string;
}

export type FileId = number & { __marker: FileId };

export interface FullSourceRange extends SourceRange {
    readonly file: FileId;
}

export interface WithSourceRange<T> extends FullSourceRange {
    readonly value: T;
}

export const enum AstKind {
    IDENTIFIER,
    SYMBOL,
    EMPTY_SYMBOL,
    FN_TYPE,
    LAMBDA,
    CALL,
    PATTERN,
    TYPE_UNIVERSE,
    TYPE_UNIVERSE_SUBSCRIPT,
}

export type Ast =
    | AstIdentifier
    | AstSymbol
    | AstEmptySymbol
    | AstLambda
    | AstFnType
    | AstCall
    | AstPattern
    | AstTypeUniverse
    | AstTypeUniverseSubscript
;

export interface AstIdentifier extends SourceRange {
    readonly kind: AstKind.IDENTIFIER;
    readonly name: string;
}

export interface AstSymbol {
    readonly kind: AstKind.SYMBOL;
    readonly path: AstIdentifier[];
    readonly prefixEmpty?: AstEmptySymbol;
}

export interface AstEmptySymbol extends SourceRange {
    readonly kind: AstKind.EMPTY_SYMBOL;
}

export interface AstLambda {
    readonly kind: AstKind.LAMBDA;
    readonly name: AstIdentifier;
    readonly body: Ast;
}

export interface AstFnType {
    readonly kind: AstKind.FN_TYPE;
    readonly outputType: Ast;
    readonly inputType: Ast;
    readonly arg?: AstIdentifier;
}

export interface AstCall {
    readonly kind: AstKind.CALL;
    readonly fn: Ast;
    readonly args: Ast[];
}

export interface AstPattern extends SourceRange {
    readonly kind: AstKind.PATTERN;
    readonly name: AstIdentifier;
}

export interface AstTypeUniverse extends SourceRange {
    readonly kind: AstKind.TYPE_UNIVERSE;
    readonly subscript: Ast;
}

export interface AstTypeUniverseSubscript extends SourceRange {
    readonly kind: AstKind.TYPE_UNIVERSE_SUBSCRIPT;
    readonly value: number;
}

export interface AstDeclaration {
    readonly lhs: Ast;
    readonly type?: Ast;
    readonly rhs?: Ast;
    readonly checkOnly: boolean;
}

export interface ExpressionDeclaration {
    readonly patterns: Set<Symbol>;
    readonly lhs: Expression;
    readonly type?: Expression;
    readonly rhs?: Expression;
    readonly checkOnly: boolean;
}

export interface AstFile {
    readonly declarations: AstDeclaration[];
    readonly assignments: [Ast, Ast][];
}


function asSourceRange(r: SourceRange): SourceRange {
    return {start: r.start, length: r.length};
}

class SourceRangeBuilder {
    start: number = 0;
    length: number = 0;
    hasMerge = false;
    merge(range: SourceRange) {
        if (!this.hasMerge) {
            this.start = range.start;
            this.length = range.length;
            this.hasMerge = true;
        } else {
            if (this.start > range.start) {
                this.start = range.start;
            }
            if (this.start + this.length < range.start + range.length) {
                this.length = range.start + range.length - this.start;
            }
        }
    }
    mergeAst(...todo: Ast[]) {
        while (todo.length > 0) {
            const ast = todo.pop()!;
            switch (ast.kind) {
                case AstKind.CALL:
                    pushReversed(todo, ast.args);
                    todo.push(ast.fn);
                    break;
                case AstKind.FN_TYPE:
                    todo.push(ast.outputType, ast.inputType);
                    if (ast.arg !== void 0) {
                        todo.push(ast.arg);
                    }
                    break;
                case AstKind.EMPTY_SYMBOL:
                    this.merge(ast);
                    break;
                case AstKind.LAMBDA:
                    todo.push(ast.body, ast.name);
                    break;
                case AstKind.SYMBOL:
                    for (const name of ast.path) {
                        this.merge(name);
                    }
                    break;
                case AstKind.PATTERN:
                case AstKind.IDENTIFIER:
                    this.merge(ast);
                    break;
            }
        }
    }
    asSourceRange(): SourceRange {
        assert(this.hasMerge);
        return {start: this.start, length: this.length};
    }
}

function getSourceRange(...asts: Ast[]): SourceRange {
    const builder = new SourceRangeBuilder();
    builder.mergeAst(...asts);
    return builder.asSourceRange();
}

export function parse(source: string) {
    const parser = new Parser(source);
    return parser.parse() ?? parser.diagnostics;
}

type ParserTodo = (self: Parser) => void;

export class Parser {
    readonly diagnostics: ParseDiagnostic[] = [];
    private readonly todo: ParserTodo[] = [];
    private readonly astStack: Ast[] = [];
    private cursor = 0;
    private token: Token = {kind: TokenKind.EOF, text: '', ...UNKNOWN_SOURCERANGE};
    private lah: (Token | null)[] = [];
    constructor(private readonly source: string) {}
    private _scanNextToken(): Token | null {
        while (this.cursor < this.source.length && isWhitespace(this.source.charCodeAt(this.cursor))) {
            this.cursor++;
        }
        const start = this.cursor;
        const self = this;
        function tk(kind: TokenKind): Token {
            return {
                kind,
                text: '',
                start,
                length: self.cursor - start,
            };
        }
        if (this.cursor >= this.source.length) {
            return tk(TokenKind.EOF);
        }
        switch (this.source.charCodeAt(this.cursor)) {
            case CCODE_COLON: this.cursor++; return tk(TokenKind.COLON);
            case CCODE_EQUAL:
                this.cursor++;
                if (this.cursor < this.source.length + 1 && this.source.charCodeAt(this.cursor) === CCODE_EQUAL && this.source.charCodeAt(this.cursor + 1) === CCODE_EQUAL) {
                    this.cursor += 2;
                    return tk(TokenKind.EQUIV);
                } else {
                    return tk(TokenKind.ASSIGN);
                }
            case CCODE_OPEN_PARENTH: this.cursor++; return tk(TokenKind.OPEN_PARENTH);
            case CCODE_CLOSE_PARENTH: this.cursor++; return tk(TokenKind.CLOSE_PARENTH);
            case CCODE_OPEN_BRACKET: this.cursor++; return tk(TokenKind.OPEN_BRACKET);
            case CCODE_CLOSE_BRACKET: this.cursor++; return tk(TokenKind.CLOSE_BRACKET);
            case CCODE_COMMA: this.cursor++; return tk(TokenKind.COMMA);
            case CCODE_DOT: this.cursor++; return tk(TokenKind.DOT);
            case CCODE_EAR: this.cursor++; return tk(TokenKind.EAR);
            case CCODE_SEMI_COLON: this.cursor++; return tk(TokenKind.SEMI_COLON);
            case CCODE_DASH:
                this.cursor++;
                if (this.source.charCodeAt(this.cursor) === CCODE_GT) {
                    this.cursor++;
                    return tk(TokenKind.ARROW);
                } else {
                    return {
                        kind: TokenKind.OPERATOR,
                        text: '-',
                        start,
                        length: this.cursor - start,
                    };
                }
            case CCODE_BSLASH:
                this.cursor++;
                return tk(TokenKind.BSLASH);
            default: {
                if (isDigit(this.source.charCodeAt(this.cursor))) {
                    const c = this.cursor;
                    let value = 0;
                    while (this.cursor < this.source.length && isDigit(this.source.charCodeAt(this.cursor))) {
                        value *= 10;
                        value += this.source.charCodeAt(this.cursor) - CCODE_0;
                        this.cursor++;
                    }
                    if (this.source.charCodeAt(this.cursor) === CCODE_L) {
                        this.cursor++;
                        return {
                            kind: TokenKind.NUMBER,
                            text: '',
                            value,
                            start,
                            length: this.cursor - start,
                        };
                    } else {
                        this.cursor = c;
                    }
                }
                if (isIdentifierPart(this.source.charCodeAt(this.cursor))) {
                    let text = '';
                    while (this.cursor < this.source.length && isIdentifierPart(this.source.charCodeAt(this.cursor))) {
                        text += this.source.charAt(this.cursor);
                        this.cursor++;
                    }
                    if (KEYWORKDS.hasOwnProperty(text)) {
                        return tk(KEYWORKDS[text]);
                    } else return {
                        kind: TokenKind.IDENTIFIER,
                        text,
                        start,
                        length: this.cursor - start,
                    };
                } else {
                    this.diagnostics.push({
                        msg: 'unexpected character ' + this.source.charAt(this.cursor),
                        start,
                        length: 1,
                    });
                    return null;
                }
            }
        }
    }
    private nextToken(): ParserTodo {
        return self => {
            if (self.lah.length > 0) {
                self.token = self.lah.shift()!;
            } else {
                const token = self._scanNextToken();
                if (token !== null) {
                    self.token = token;
                }
            }
        };
    }
    private doLah(count: number): ParserTodo {
        return self => {
            while (self.lah.length < count) {
                const token = self._scanNextToken();
                if (token !== null) {
                    self.lah.push(token);
                }
            }
        };
    }
    private clearLah() {
        if (this.lah.length > 0) {
            this.token = this.lah[this.lah.length - 1] ?? panic();
            this.lah.length = 0;
        }
    }
    private expect(tk: TokenKind): ParserTodo {
        return self => {
            if (self.token.kind === tk) {
                self.doInOrder(self.nextToken());
            } else {
                self.diagnostics.push({
                    msg: `unexpected token`,
                    ...asSourceRange(self.token),
                });
            }
        };
    }
    private unexpected() {
        this.diagnostics.push({
            msg: `unexpected token`,
            ...asSourceRange(this.token),
        });
    }
    private doInOrder(...actions: ParserTodo[]) {
        pushReversed(this.todo, actions);
    }
    private parseIdentifier(): ParserTodo {
        return self => {
            if (self.token.kind === TokenKind.IDENTIFIER) {
                self.astStack.push({kind: AstKind.IDENTIFIER, name: self.token.text, ...asSourceRange(self.token)});
                self.doInOrder(self.nextToken());
            } else this.unexpected();
        };
    }
    private parseExpression(): ParserTodo {
        return self => {
            if (self.token.kind === TokenKind.BSLASH) {
                self.doInOrder(
                    self.nextToken(),
                    self.parseIdentifier(),
                    self.parseExpression(),
                    self => {
                        const expr = self.astStack.pop()!;
                        const name = self.astStack.pop()!;
                        assert(name.kind === AstKind.IDENTIFIER);
                        self.astStack.push({kind: AstKind.LAMBDA, name, body: expr});
                    },
                );
            } else self.doInOrder(self.parseFunctionType());
        };
    }
    private parseFunctionType(): ParserTodo {
        return self => {
            if (self.token.kind === TokenKind.OPEN_PARENTH) {
                self.doInOrder(self.doLah(2), self => {
                    if (self.lah[0] !== null && self.lah[1] !== null && self.lah[0].kind === TokenKind.IDENTIFIER && self.lah[1].kind === TokenKind.COLON) {
                        const arg: AstIdentifier = {kind: AstKind.IDENTIFIER, name: self.lah[0].text, ...asSourceRange(self.lah[0])};
                        self.clearLah();
                        self.doInOrder(
                            self.nextToken(),
                            self.parseExpression(),
                            self.expect(TokenKind.CLOSE_PARENTH),
                            self.expect(TokenKind.ARROW),
                            self.parseExpression(),
                            self => {
                                const outputType = self.astStack.pop()!;
                                const inputType = self.astStack.pop()!;
                                self.astStack.push({kind: AstKind.FN_TYPE, arg, inputType, outputType});
                            },
                        );
                    } else self.parseNonDependentFunctionType();
                });
            } else self.parseNonDependentFunctionType();
        };
    }
    private parseNonDependentFunctionType() {
        this.doInOrder(this.parseCallExpression(), self => {
            if (self.token.kind === TokenKind.ARROW) {
                const inputType = self.astStack.pop()!;
                self.doInOrder(self.nextToken(), self.parseExpression(), self => {
                    const outputType = self.astStack.pop()!;
                    self.astStack.push({kind: AstKind.FN_TYPE, inputType, outputType});
                });
            }
        });
    }
    private parseCallExpression(): ParserTodo {
        return self => {
            self.doInOrder(self.parsePrimitiveExpression(), self => {
                if (self.token.kind === TokenKind.OPEN_PARENTH) {
                    self.doInOrder(self.parseCallExpressionRest(self.astStack.pop()!));
                }
            });
        };
    }
    private parseCallExpressionRest(fn: Ast): ParserTodo {
        const args: Ast[] = [];
        function doIt(self: Parser) {
            if (self.token.kind === TokenKind.OPEN_PARENTH) {
                self.doInOrder(self.parseArgList(args), doIt);
            } else {
                self.astStack.push({kind: AstKind.CALL, fn, args});
            }
        }
        return doIt;
    }
    private parseArgList(args: Ast[]): ParserTodo {
        function parseRest(self: Parser) {
            args.push(self.astStack.pop()!);
            if (self.token.kind === TokenKind.COMMA) {
                self.doInOrder(self.nextToken(), self => {
                    if (self.token.kind !== TokenKind.CLOSE_PARENTH) {
                        self.doInOrder(self.parseExpression(), parseRest);
                    } else {
                        self.doInOrder(self.nextToken());
                    }
                });
            } else {
                self.doInOrder(self.expect(TokenKind.CLOSE_PARENTH));
            }
        }
        return self => {
            self.doInOrder(self.expect(TokenKind.OPEN_PARENTH), self.parseExpression(), parseRest);
        };
    }

    private parsePrimitiveExpression(): ParserTodo {
        return self => {
            const token = self.token;
            switch (token.kind) {
                case TokenKind.IDENTIFIER: self.doInOrder(this.parseSymbol()); break;
                case TokenKind.OPEN_PARENTH: self.doInOrder(self.nextToken(), self.parseExpression(), self.expect(TokenKind.CLOSE_PARENTH)); break;
                case TokenKind.TYPE: {
                    const typeToken = asSourceRange(token);
                    self.doInOrder(self.nextToken(), self.expect(TokenKind.OPEN_PARENTH), self.parseExpression(), self.expect(TokenKind.CLOSE_PARENTH), self => {
                        self.astStack.push({kind: AstKind.TYPE_UNIVERSE, subscript: self.astStack.pop()!, ...typeToken});
                    });
                    break;
                }
                case TokenKind.NUMBER: {
                    self.astStack.push({kind: AstKind.TYPE_UNIVERSE_SUBSCRIPT, value: token.value ?? panic(), ...asSourceRange(token)});
                    self.doInOrder(self.nextToken());
                    break;
                }
                case TokenKind.EAR: {
                    const ear = asSourceRange(token);
                    self.doInOrder(self.nextToken(), self.parseIdentifier(), self => {
                        const name = self.astStack.pop()!;
                        assert(name.kind === AstKind.IDENTIFIER);
                        self.astStack.push({kind: AstKind.PATTERN, name, ...ear});
                    });
                    break;
                }
                default: self.unexpected(); break;
            }
        }
    }
    private parseSymbol(): ParserTodo {
        const path: AstIdentifier[] = [];
        function parseRest(self: Parser) {
            const name = self.astStack.pop()!;
            assert(name.kind === AstKind.IDENTIFIER);
            path.push(name);
            if (self.token.kind === TokenKind.DOT) {
                self.doInOrder(self.nextToken(), self.parseIdentifier(), parseRest);
            } else {
                self.astStack.push(path.length === 1 ? path[0] : {kind: AstKind.SYMBOL, path});
            }
        }
        return self => {
            self.doInOrder(self.parseIdentifier(), parseRest);
        };
    }
    private wait() {
        while (this.todo.length > 0) {
            if (this.diagnostics.length > 0) {
                return;
            }
            this.todo.pop()!(this);
        }
    }
    private parseOptionalSemicolon(): ParserTodo {
        return self => {
            if (self.token.kind === TokenKind.SEMI_COLON) {
                self.doInOrder(self.nextToken(), self.parseOptionalSemicolon());
            }
        };
    }
    private parseFileItem(file: AstFile): ParserTodo {
        let type: Ast | undefined = void 0;
        let rhs: Ast | undefined = void 0;
        let checkOnly = false;
        return self => {
            self.doInOrder(self.parseExpression(), self => {
                switch (self.token.kind) {
                    case TokenKind.COLON:
                        self.doInOrder(self.nextToken(), self => {
                            if (self.token.kind !== TokenKind.ASSIGN && self.token.kind !== TokenKind.EQUIV) {
                                self.doInOrder(self.parseExpression(), self => {
                                    type = self.astStack.pop()!;
                                });
                            }
                        }, self => {
                            if (self.token.kind === TokenKind.ASSIGN || self.token.kind === TokenKind.EQUIV) {
                                checkOnly = self.token.kind === TokenKind.EQUIV;
                                self.doInOrder(self.nextToken(), self.parseExpression(), self => {
                                    rhs = self.astStack.pop()!;
                                });
                            }
                        }, self => {
                            const lhs = self.astStack.pop() ?? panic();
                            file.declarations.push({lhs, type, rhs, checkOnly});
                        });
                        break;
                    case TokenKind.ASSIGN:
                        self.doInOrder(self.nextToken(), self.parseExpression(), self => {
                            const rhs = self.astStack.pop()!;
                            const lhs = self.astStack.pop()!;
                            file.assignments.push([lhs, rhs]);
                        });
                        break;
                    default: file.declarations.push({lhs: self.astStack.pop()!, rhs, type, checkOnly: false});
                }
            }, self.parseOptionalSemicolon());
        };
    }
    private parseFile(file: AstFile): ParserTodo {
        function doIt(self: Parser) {
            if (self.token.kind !== TokenKind.EOF) {
                self.doInOrder(self.parseFileItem(file), doIt);
            }
        }
        return doIt;
    }
    parse() {
        const file: AstFile = {declarations: [], assignments: []};
        const token = this._scanNextToken();
        if (token === null) return null;
        this.token = token;
        this.doInOrder(this.parseFile(file));
        this.wait();
        if (this.diagnostics.length === 0) {
            return file;
        } else return null;
    }
}

interface Scope {
    readonly symbol: Symbol;
    readonly letVariables: Map<string, Symbol>;
}

export function analyse(context: SymbolRegistry, outermostSymbol: Symbol, file: AstFile, fileId: FileId, maxIterations: number, logger: ExpressionLogger) {
    const scopes: Scope[] = [{
        symbol: outermostSymbol,
        letVariables: new Map(),
    }];
    const diagnostics: ParseDiagnostic[] = [];
    const newSymbols: Set<Symbol> = new Set();
    const constraintSolver = new ConstraintSolver(context, logger);

    const generatedSymbol = context.getSymbol(null, "generated", true) ?? panic();

    return run(maxIterations);

    function run(maxIterations: number): [ParseDiagnostic[], Diagnostic[]] {
        loadFile(file, fileId);
        if (diagnostics.length > 0) {
            newSymbols.forEach(s => context.removeSymbol(s));
        }
        const d = constraintSolver.run(maxIterations);
        if (d.length > 0) {
            newSymbols.forEach(s => context.removeSymbol(s));
        }
        return [diagnostics, d];
    }

    function getGeneratedSymbol(name: string) {
        const [ret, success] = context.addNewSymbol(generatedSymbol, name, true) ?? panic();
        if (success) {
            newSymbols.add(ret);
        }
        return ret;
    }

    function addSymbol(parent: Symbol, name: AstIdentifier) {
        const [symbol, success] = context.addNewSymbol(parent, name.name, false);
        if (success) {
            newSymbols.add(symbol);
            constraintSolver.unlockSymbol(symbol);
        } else if (!newSymbols.has(symbol)) {
            diagnostics.push({
                msg: `cannot redefine symbol ${name.name}`,
                ...asSourceRange(name),
            });
            return null;
        }
        return symbol;
    }

    function prepareSymbol(expr: Ast) {
        const scope = scopes[scopes.length - 1];
        switch (expr.kind) {
            case AstKind.IDENTIFIER: return addSymbol(scope.symbol, expr);
            case AstKind.SYMBOL: {
                let symbol = scope.symbol;
                for (const name of expr.path) {
                    const s = addSymbol(symbol, name);
                    if (s === null) {
                        return null;
                    }
                    symbol = s;
                }
                return symbol;
            }
        }
        return null;
    }

    function collectAndCreatePatternSymbols(expr: Ast) {
        const todo = [expr];
        const names: Set<string> = new Set();
        while (todo.length > 0) {
            const expr = todo.pop()!;
            switch (expr.kind) {
                case AstKind.PATTERN:
                    if (expr.name !== void 0) {
                        names.add(expr.name.name);
                    }
                    break;
                case AstKind.CALL:
                    pushReversed(todo, expr.args);
                    todo.push(expr.fn);
                    break;
            }
        }
        const ret: Set<Symbol> = new Set();
        names.forEach(name => {
            ret.add(getGeneratedSymbol(name));
        });
        return ret;
    }

    function resolveIdentifier(name: string, fnArgScope: Symbol[] | null, patternSymbols: Set<Symbol> | null) {
        if (fnArgScope !== null) {
            for (let i = 0; i < fnArgScope.length; i++) {
                const symbol = fnArgScope[fnArgScope.length - 1 - i];
                if (name === context.getSymbolEntry(symbol).name) {
                    return symbol;
                }
            }
        }
        if (patternSymbols !== null) {
            const patternSymbol = context.getSymbol(generatedSymbol, name, false);
            if (patternSymbol !== null && patternSymbols.has(patternSymbol)) return patternSymbol;
        }
        for (let i = 0; i < scopes.length; i++) {
            const scope = scopes[scopes.length - 1 - i];
            if (scope.letVariables.has(name)) {
                return scope.letVariables.get(name)!;
            } else {
                const symbol = context.getSymbol(scope.symbol, name, false);
                if (symbol !== null) {
                    return symbol;
                }
            }
        }
        return context.getSymbol(null, name, false);
    }

    function resolveSymbol(expr: AstSymbol) {
        const firstName = expr.path[0];
        let first = resolveIdentifier(firstName.name, null, null);
        if (first === null) {
            diagnostics.push({
                msg: `undefined identifier ${firstName.name}`,
                ...asSourceRange(firstName),
            });
            return null;
        }
        for (let i = 1, a = expr.path; i < a.length; i++) {
            const name = a[i];
            const s = context.getSymbol(first, name.name, false);
            if (s === null) {
                diagnostics.push({
                    msg: `undefined member ${name.name}`,
                    ...asSourceRange(name),
                });
            }
            first = s;
        }
        return first;
    }

    function convertExpression(expr: Ast, patternSymbols: Set<Symbol> | null) {
        const todo: (Ast | ((stack: Expression[]) => void))[] = [expr];
        const stack: Expression[] = [];
        const fnArgScope: Symbol[] = [];
        while (todo.length > 0) {
            const t = todo.pop()!;
            if (typeof t === 'function') {
                t(stack);
            } else switch (t.kind) {
                case AstKind.CALL: {
                    const length = t.args.length;
                    todo.push(stack => {
                        const args: Expression[] = [];
                        popReversed(stack, args, length);
                        const fn = stack.pop()!;
                        stack.push({kind: ExpressionKind.CALL, fn, args});
                    });
                    pushReversed(todo, t.args);
                    todo.push(t.fn);
                    break;
                }
                case AstKind.PATTERN: {
                    const symbol = getGeneratedSymbol(t.name.name);
                    if (patternSymbols !== null) {
                        patternSymbols.add(symbol);
                    }
                    stack.push({kind: ExpressionKind.SYMBOL, symbol, ...asSourceRange(t.name)});
                    break;
                }
                case AstKind.EMPTY_SYMBOL: {
                    if (scopes.length > 0) {
                        stack.push({kind: ExpressionKind.SYMBOL, symbol: scopes[scopes.length - 1].symbol, ...asSourceRange(t)});
                    } else {
                        diagnostics.push({
                            msg: 'cannot use . here',
                            ...asSourceRange(t),
                        });
                        return null;
                    }
                    break;
                }
                case AstKind.IDENTIFIER: {
                    const symbol = resolveIdentifier(t.name, fnArgScope, patternSymbols);
                    if (symbol !== null) {
                        stack.push({kind: ExpressionKind.SYMBOL, symbol, ...asSourceRange(t)});
                    } else {
                        diagnostics.push({
                            msg: 'undefined identifier ' + t.name,
                            ...asSourceRange(t),
                        });
                        return null;
                    }
                    break;
                }
                case AstKind.FN_TYPE: {
                    if (t.arg !== void 0) {
                        const symbol = getGeneratedSymbol(t.arg.name);
                        fnArgScope.push(symbol);
                        todo.push(stack => {
                            const outputType = stack.pop()!;
                            const inputType = stack.pop()!;
                            stack.push({
                                kind: ExpressionKind.FN_TYPE,
                                inputType,
                                outputType,
                                arg: symbol,
                            });
                            fnArgScope.pop();
                        }, t.outputType, t.inputType);
                    } else {
                        todo.push(stack => {
                            const outputType = stack.pop()!;
                            const inputType = stack.pop()!;
                            stack.push({
                                kind: ExpressionKind.FN_TYPE,
                                inputType,
                                outputType,
                            });
                        }, t.outputType, t.inputType);
                    }
                    break;
                }
                case AstKind.LAMBDA: {
                    const symbol = getGeneratedSymbol(t.name.name);
                    fnArgScope.push(symbol);
                    todo.push(stack => {
                        const body = stack.pop()!;
                        fnArgScope.pop();
                        stack.push({kind: ExpressionKind.LAMBDA, body, arg: symbol});
                    }, t.body);
                    break;
                }
                case AstKind.PATTERN: {
                    const symbol = getGeneratedSymbol(t.name.name);
                    if (patternSymbols !== null) {
                        patternSymbols.add(symbol);
                    }
                    stack.push({kind: ExpressionKind.SYMBOL, symbol, ...asSourceRange(t.name)});
                    break;
                }
                case AstKind.SYMBOL: {
                    const symbol = resolveSymbol(t);
                    if (symbol === null) {
                        return null;
                    }
                    stack.push({kind: ExpressionKind.SYMBOL, symbol, ...asSourceRange(t.path[0])});
                    break;
                }
                case AstKind.TYPE_UNIVERSE: {
                    todo.push(stack => {
                        stack.push({kind: ExpressionKind.UNIVERSE, subscript: stack.pop()!});
                    }, t.subscript);
                    break;
                }
                case AstKind.TYPE_UNIVERSE_SUBSCRIPT: {
                    stack.push({kind: ExpressionKind.LEVEL, value: t.value});
                    break;
                }
                default: panic();
            }
        }
        assert(stack.length === 1);
        return stack[0];
    }

    function processOneDeclaration(decl: ExpressionDeclaration) {
        let {lhs, rhs, type, patterns, checkOnly} = decl;
        const reps = new Map<Symbol, Expression>();
        patterns.forEach(symbol => {
            reps.set(symbol, symbolExpression(constraintSolver.registry.createTempSymbol(true, null), null));
        });
        const lhsRep = replaceSymbols(lhs, reps);
        const rhsRep = rhs !== void 0 ? replaceSymbols(rhs, reps) : void 0;
        if (type !== void 0) {
            constraintSolver.addTypeTypeConstraint(type);
        } else {
            type = symbolExpression(constraintSolver.createTypeSymbol(false), null);
        }
        constraintSolver.addTypeConstraint(lhsRep, type);

        out: if (rhs !== void 0) {
            if (!checkOnly && lhs.kind === ExpressionKind.SYMBOL) {
                const entry = context.getSymbolEntry(lhs.symbol);
                if (entry.ownValue === void 0) {
                    entry.ownValue = rhs;
                    break out;
                }
            }
            if (rhsRep !== void 0) {
                constraintSolver.addEqualConstraint(lhsRep, rhsRep);
            }
        }
        if (!checkOnly && rhs !== void 0 && lhs.kind === ExpressionKind.CALL && lhs.fn.kind === ExpressionKind.SYMBOL && newSymbols.has(lhs.fn.symbol)) {
            const entry = context.getSymbolEntry(lhs.fn.symbol);
            if (entry.downValue === void 0) {
                entry.downValue = [];
            }
            entry.downValue.push({lhs, rhs, patterns});
        }
    }

    function loadFile(file: AstFile, fileName: FileId) {
        const exprs: Expression[] = [];
        for (const decl of file.declarations) {
            prepareSymbol(decl.lhs);
        }
        if (diagnostics.length > 0) return exprs;
        const decls: ExpressionDeclaration[] = [];
        for (const decl of file.declarations) {
            const patterns = new Set<Symbol>();
            const lhsExpr = convertExpression(decl.lhs, patterns);
            if (lhsExpr === null) {
                return exprs;
            }
            const type = decl.type !== void 0 ? convertExpression(decl.type, null) : null;
            if (diagnostics.length > 0) return exprs;

            const rhsExpr = decl.rhs !== void 0 ? convertExpression(decl.rhs, patterns) : null;
            decls.push({lhs: lhsExpr, rhs: rhsExpr ?? void 0, type: type ?? void 0, patterns, checkOnly: decl.checkOnly});
        }
        for (const decl of decls) {
            processOneDeclaration(decl);
        }
        return exprs;
    }
}
