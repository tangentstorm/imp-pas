{$mode objfpc}{$H+}
program minlisp(input, output);
uses arrays, ascii, sysutils;

type
  TKind	= (kNUL, kERR, kINT, kSYM, kSTR, kCEL);
  TItem	= record
	    kind : TKind;
	    data : integer;
	  end;	 
  TCell	= record
	    car, cdr : TItem
	  end;	     
  TBind	= record // variable binding
	    symid : cardinal;
	    attrs : TItem;
	    value : TItem;
	  end;
  TSymTbl = specialize GEqArray<string>;
  TValTbl = specialize GArray<TBind>;
  TCelTbl = specialize GArray<TCell>;
  TFunc	= function( cell : TCell ) : TCell;

function NextChar(out ch : char) : char;
  begin
    Read( ch ); result := ch;
  end;

var
  ch   : char = #0;
  nest : string = '';
  syms : TSymTbl;
  cels : TCelTbl;
  vals : TValTbl;
  null : TItem;

const
  whitespace  = [#0..' '] - [^C, ^D];
  stopchars   = whitespace + ['(',')','[',']','{','}', '"', ''''];
  commentChar = '#';

function Item( kind : TKind; data : cardinal ) : TItem;
  begin
    result.kind := kind;
    result.data := data;
  end;

function Sym( s : string ) : cardinal;
  begin
    if not syms.Find( s, result ) then result := syms.Append( s );
  end;

function Cons( head, tail : TItem ) : TItem;
  var cell : TCell;
  begin
    cell.car := head;
    cell.cdr := tail;
    result := Item( kCel, cels.Append( cell ));
  end;

// this recognizes decimal integers.
function IsNum( s : string; out num : integer ) : boolean;
  var i : cardinal = 1; negate : boolean = false;
  begin
    result := true; num := 0;
    if s[1] = '-' then begin inc(i); negate := true; end;
    while result and (i <= length(s)) do
      if s[i] in ['0'..'9'] then
	num := num * 10 + ord(s[i]) - ord('0')
      else result := false;
    if result and negate then num := -num;
  end;

function ReadAtom : TItem;
  var tok : string = ''; i : integer;
  begin
    repeat tok := tok + ch until NextChar(ch) in stopchars;
    if IsNum( tok, i ) 
      then result := Item( kINT, i )
      else result := Item( kSYM, Sym( tok ))
  end;

function PopChar( var s : string ) : char;
  var last : integer; ch : char;
  begin
    last := Length(s);
    if last < 0 then ch := #0 else ch := s[ last ];
    SetLength( s, last - 1 );
    result := ch;
  end;

function ReadString : TItem;
  var s : string = '';
  begin
    nest += '"';
    while NextChar(ch) <> '"' do
      if ch = '\' then
	case NextChar(ch) of
	  '0' : s := s + #0;
	  't' : s := s + ^I;
	  'n' : s := s + LineEnding;
	  else s := s + ch;
	end
      else s := s + ch;
    PopChar(nest);
    result := Item(kSTR, Sym(s))
  end;

procedure SkipCommentsAndWhitespace;
  begin
    while ch in whitespace do
      if NextChar(ch) = commentChar then
	repeat until NextChar(ch) = ascii.lf
  end;

function ReadListEnd : TItem;
  var expect : char;
  begin
    if Length(nest) = 0 then
      result := Item(kERR, Sym('Unexpected char: ' + ch))
    else begin
      case PopChar(nest) of
	'{' : expect := '}';
	'[' : expect := ']';
	'(' : expect := ')';
	else expect := '?' // should never happen
      end;
      if ch = expect then result := null
      else result := Item(kERR, Sym('List end mismatch. Expected: '
			 + expect + ', got: ' + ch));
    end;
    NextChar(ch);
  end;

function ReadNext( out value : TItem ): TItem;
  
  function ReadList( out list : TItem ) : TItem;
    var head, tail : TItem;
    begin
      nest := nest + ch;
      SkipCommentsAndWhitespace;
      if ch in [')', ']', '}'] then result := ReadListEnd
      else if ReadNext(head).kind = kERR then result := head
      else if ReadList(tail).kind = kERR then result := tail
      else result := Cons(head, tail);
      PopChar(nest);
      list := result;
    end; { ReadList }
  
  function ReadQuote : TItem;
    begin
      if ReadNext(result).kind <> kERR
	then result := Cons(Item(kSym, Sym('quote')), result)
    end; { ReadQuote }
  
  begin
    SkipCommentsAndWhitespace;
    case ch of
      '(','[','{' : ReadList(result);
      ')',']','}' : result := ReadListEnd;
      '"'	  : result := ReadString;
      ''''	  : result := ReadQuote;
      else result := ReadAtom;
    end;
    value := result;
  end; { ReadNext }

function Eval( item : TItem ) : TItem;
  begin
    result := item
  end;

function ShowItem( item : TItem ) : string;

  function ShowList( ref : TItem; AtHead : boolean) : string;
    var cell : TCell;
    begin
      if AtHead then result := '(' else result := ' ';
      cell := cels[ ref.data ];
      result += ShowItem( cell.car );
      case cell.cdr.kind of
	kNUL : AppendStr( result, ')' );
	kCEL : AppendStr( result, ShowList( cell.cdr, false ));
	else   AppendStr( result, '. ' + ShowItem( cell.cdr ));
      end;
    end; { ShowList }

  begin
    case item.kind of
      kERR,
      kSYM : result := syms[ item.data ];
      kSTR : result := '"' + syms[ item.data ] + '"';
      kINT : result := IntToStr( item.data );
      kCEL : result := ShowList( item, true );
    end
  end; { ShowItem }

procedure Print( item : TItem );
  begin
    WriteLn(ShowItem(item));
  end;

var val : TItem;
begin
  syms := TSymTbl.Create;
  cels := TCelTbl.Create;
  vals := TValTbl.Create;
  null := Item(kNUL, 0);
  repeat Print(Eval(ReadNext(val)))
  until (val.kind = kERR)
end.
