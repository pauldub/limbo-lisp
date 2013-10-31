implement Lisp;
include "sys.m";
	sys: Sys;
include "lists.m";
	lists: Lists;
include "draw.m";
include "sexprs.m";
	sexprs: Sexprs;
	Sexp: import Sexprs;
include "string.m";
	str: String;

# Port of yoctolisp to limbo 
# charon https://github.com/fragglet/yoctolisp/blob/master/yoctolisp.md

# TODO:
#   - Use inferno builtin s-expression parser :)
#   - Implement all yoctolisp
#   - Improve it (use inferno's builtin garbage collector? :)
#   - Use it
isspace(c: byte) : int
{
	return int c == ' ';
}

issym(char: byte) : int
{
	return str->in(int char, "^ ()[]{}\",'`;#|\\") == 1;
}

isdigit(char: byte) : int
{
	return str->in(int char, "0-9") == 1;
}

Lisp: module
{
	TOKEN_OPEN_PAREN, TOKEN_CLOSE_PAREN, TOKEN_SYMBOL, TOKEN_QUOTE,
TOKEN_NUMBER, TOKEN_STRING, TOKEN_BOOLEAN, TOKEN_ERROR, TOKEN_EOF: con iota;

	init:	fn(ctx: ref Draw->Context, args: list of string);

	Value: adt {
		next: 	cyclic ref Value;

		pick {
			String or Symbol =>
				val: string;
			Number or Boolean =>
				val: int;
			Cell =>
				cdr: cyclic ref Value.Cell;
				car: cyclic ref Value;
			Context =>
				parent: cyclic ref Value.Context;
				vars: cyclic ref Value.Cell;
			Function =>
				context: cyclic ref Value.Context;
				code: cyclic ref Value.Cell;
		}
		
		# Links a value to a lexer's values linked list
		alloc: 		fn(value: self ref Value);
		Print:	fn(value: self ref Value);
	};

	Lexer: adt {
		buf: 				array of byte;
		position:		int;
		symbols: 		list of ref Value.Symbol;
		value:			ref Value;

		alloc: 			fn(str: string) : 	ref Lexer;


		# Read byte from buf at current position
		ReadBuf:					fn(lexer: self ref Lexer) : byte;

		ParseList: 				fn(lexer: self ref Lexer) : ref Value;
		ParseQuoted: 			fn(lexer: self ref Lexer) : ref Value;
		SymbolForName: 		fn(lexer: self ref Lexer, name: string) : ref Value;
		ParseFromToken: 	fn(lexer: self ref Lexer, token: int) : ref Value;

		# Read token from buf at current position
		ReadToken: 	fn(lexer: self ref Lexer) : int;
		# Read string terminated by " from buf at current position
		# might go private?
		ReadString: 	fn(lexer: self ref Lexer) : int;

	};

	rootContext: 	ref Value.Context;
	values:				ref Value;

	alloc:				fn(s: string) : ref Value;

	cons: 				fn(car: ref Value, cdr: ref Value.Cell) : ref Value.Cell;

	eval: 									fn(context: ref Value.Context, code: ref Value) : ref Value;
	evalList: 							fn(context: ref Value.Context, code: ref Value.Cell) : ref Value;
	# evalFunctionCall: 		fn(context: ref Value.Context, code: ref Value) : ref Value;

	parse: 									fn(s: string) : ref Value;
};

Value.alloc(value: self ref Value)
{
	value.next = values;
	values = value;
}

Value.Print(value: self ref Value)
{
	pick val := value {
	String =>
		sys->print("\"%s\"", val.val);
	Number =>
		sys->print("%d", val.val);
	Boolean =>
		if (val.val == 1) sys->print("true");
		else sys->print("false");
	Symbol =>
		sys->print("%s", val.val);
	Cell =>
		sys->print("(");
		while (val != nil) {
			val.car.Print();
			val = val.cdr;

			if (val != nil) {
				sys->print(" ");
			}
		}
		sys->print(")");
	* =>
		sys->print("nil");
	}
}

Lexer.alloc(str: string) : ref Lexer
{
	return ref Lexer(array of byte str, 0, nil, nil);
}

Lexer.ReadBuf(lexer: self ref Lexer) : byte
{
	return lexer.buf[lexer.position];
}

Lexer.ParseList(lexer: self ref Lexer) : ref Value 
{
	result, rover: ref Value.Cell;

	for (;;) {
		token := lexer.ReadToken();
		if (token == TOKEN_EOF || token == TOKEN_ERROR)
			return nil;
		if (token == TOKEN_CLOSE_PAREN)
			break;

		cell := ref Value.Cell(nil, nil, nil);
		cell.car = lexer.ParseFromToken(token);
		cell.alloc();

		if (rover != nil) 
			rover.cdr = cell;

		if (result == nil)
			result = rover;

		rover = cell;
	}

	return result;
}

Lexer.ParseQuoted(lexer: self ref Lexer) : ref Value 
{
	token := lexer.ReadToken();
	return cons(lexer.SymbolForName("quote"),
										cons(lexer.ParseFromToken(token),	nil));
}

Lexer.SymbolForName(lexer: self ref Lexer, name: string) : ref Value 
{
	symbols : list of ref Value.Symbol;
	symbols = lexer.symbols;

	for (;symbols != nil; symbols = tl symbols) {
		symbol := hd symbols;
		if (symbol.val == name)
			return symbol;
	}

	value := ref Value.Symbol(nil, name);
	value.alloc();

	lexer.symbols = lists->append(lexer.symbols, value);

	return value;
}

Lexer.ParseFromToken(lexer: self ref Lexer, token: int) : ref Value 
{
		case token {
			TOKEN_OPEN_PAREN =>
				return lexer.ParseList();
			TOKEN_QUOTE =>
				return lexer.ParseQuoted();
			TOKEN_BOOLEAN or TOKEN_STRING or TOKEN_NUMBER or TOKEN_SYMBOL =>
				return values;
			# TOKEN_EOF or TOKEN_ERROR or TOKEN_CLOSE_PAREN =>
				# return nil;
		}

		return nil;
}

Lexer.ReadToken(lexer: self ref Lexer) : int
{
	while (lexer.position < len lexer.buf) {
		if (int lexer.ReadBuf() == ';') {
			do {
				if (++lexer.position >= len lexer.buf)
					return TOKEN_ERROR;
			} while (int lexer.ReadBuf() != '\n');
		} else if (!isspace(lexer.ReadBuf())) {
			break;
		}
		++lexer.position; 
	}
	
	if (lexer.position >= len lexer.buf)
		return TOKEN_ERROR;
	
	case int lexer.buf[lexer.position++] {
	'(' => 
		return TOKEN_OPEN_PAREN;
	')' => 
		return TOKEN_CLOSE_PAREN;
	'\'' => 
		return TOKEN_QUOTE;
	'#' =>
		if (str->in(int lexer.ReadBuf(), "ft") != 1)
			return TOKEN_ERROR;

		value := ref Value.Boolean(nil, int lexer.ReadBuf() == 't');
		value.alloc();

		++lexer.position;
		return TOKEN_BOOLEAN;
	'"' =>
		return lexer.ReadString();
	* => 
		--lexer.position;
	}

	# implement digits

	# implement symbols
	if (isdigit(lexer.ReadBuf()) == 1) {
		value := ref Value.Number(nil, 0);

		while (lexer.position < len lexer.buf && isdigit(lexer.ReadBuf()) == 1) {
			# TODO: Use string library to convert numbers.
			value.val *= 10;
			value.val += (int lexer.ReadBuf() - '0');

			++lexer.position;
		}

		value.alloc();

		return TOKEN_NUMBER;
	} else if (issym(lexer.ReadBuf()) == 1) {
		start := lexer.position;

		while (lexer.position < len lexer.buf && issym(lexer.ReadBuf()) == 1) {
			++lexer.position;
		}

		value := ref Value.Symbol(nil, string lexer.buf[start:lexer.position]);
		value.alloc();

		return TOKEN_SYMBOL;
	}

	return TOKEN_ERROR;
}

Lexer.ReadString(lexer: self ref Lexer) : int
{
	start := lexer.position;

	while (lexer.position < len lexer.buf && int lexer.ReadBuf() != '"') {
		++lexer.position;
	}
	
	if (lexer.position >= len lexer.buf)
		return TOKEN_ERROR;

	value := ref Value.String(nil, string lexer.buf[start:lexer.position]);
	value.alloc();

	++lexer.position;

	return TOKEN_STRING;
}

cons(car: ref Value, cdr: ref Value.Cell) : ref Value.Cell 
{
	result := ref Value.Cell(nil, nil, nil);
	result.car = car;
	result.cdr = cdr;
	result.alloc();
	return result;
}

# evalFunctionCall(context: ref Value.Context, code: ref Value) : ref Value {

# }

evalVariable(context: ref Value.Context, var: ref Value) : ref Value 
{
	v: ref Value.Cell;

	while (context != nil) {
		for (v = context.vars; v != nil; v = v.cdr) {
			pick val := v.car {
				Cell =>
					if (val.car == var)
						return v.cdr.car;
			}
		}
		context = context.parent;
	}

	sys->print("Undefined variable "); 
	var.Print();
	sys->print("\n");

	return nil;
}

setVariable(context: ref Value.Context, name: ref Value, value: ref Value.Cell) : ref Value 
{
	v: ref Value.Cell;

	for (v = context.vars; v != nil; v = v.cdr) {
		pick val := v.car {
			Cell =>
				if (val.car == name) {
					val.cdr == value;
					return value;
				}
		}
	}

	context.vars = cons(cons(name, value), context.vars);
	return value;
}

evalList(context: ref Value.Context, code: ref Value.Cell) : ref Value 
{
	pick symbol := code.car {
		Symbol =>
			if (symbol.val == "quote") {
				return code.cdr.car;
			} else if (symbol.val == "if") {
				val := eval(context, code.cdr.car);
				pick value := val {
					Boolean or Number =>
						if (value.val == 1)
							return eval(context, code.cdr.cdr.car);
						else if (code.cdr.cdr.cdr != nil)
							return eval(context, code.cdr.cdr.cdr.car);
						
						# FIXME: Check for errors;
				}
			} else if (symbol.val == "lambda") {
				result := ref Value.Function(nil, nil, nil);
				result.context = context;
				result.code = code.cdr;
				result.alloc();

				return result;
			} else if (symbol.val == "define") {
				# TODO
				pick val := eval(context, code.cdr.cdr.car) {
					Cell =>
						return setVariable(rootContext, code.cdr.car, val);
				}
			}
	}

	# return evalFunctionCall(context, code);
	return code;
}

eval(context: ref Value.Context, code: ref Value) : ref Value 
{
	pick val := code {
		Symbol =>
			return evalVariable(context, val);
		Cell =>
			return evalList(context, val);
	}

	return code;
}

parse(s: string) : ref Value
{
	lexer := Lexer.alloc(s);
	token := lexer.ReadToken();
	return lexer.ParseFromToken(token);
}

alloc(s: string) : ref Value
{

	code := parse(s);
	value := eval(rootContext, code);
	value.Print();
	return value;
}

init(ctxt: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	str = load String String->PATH;
	lists = load Lists Lists->PATH;

	sys->print("Limbo lisp!\n");

	# sexprs = load Sexprs Sexprs->PATH;
	# sexprs->init();
	# (sxp, t, err) :=sexprs-> Sexp.parse("(2 3 (3 5))");
	# sys->print("%s %s %s", sexprs->sxp.astext(), t, err);

	rootContext := ref Value.Context(nil, nil, nil);
	rootContext.alloc();

	# code := "(#t 2 '(4 3) (+ 2 1) test \"hello\" #f 53)";

	code := "(+ 2 3)";

	alloc(code);
}
