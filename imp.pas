{$mode objfpc}{$i xpc.inc}
program imp(input, output);
uses xpc, arrays, stacks, ascii, sysutils, num;

type
  TKind = (kNUL, kERR, kINT, kSYM, kSTR, kCEL);
  TItem = record
            kind : TKind;
            data : integer;
          end;
  TCell = record
            car, cdr : TItem
          end;
  TBind = record // name bindings.
            iden : integer; // index of a string
            cell : TCell;   // car=value cdr=attributes
          end;
  TSymTbl = specialize GEqArray<string>;
  TValTbl = specialize GArray<TBind>;
  TCelTbl = specialize GArray<TCell>;
  TFunc   = function( item : TItem ) : TItem;

var
  ch   : char = #0;
  nest : string = '';
  syms : TSymTbl;
  cels : TCelTbl;
  vals : TValTbl;
var { common symbols }
  NullSym : TItem;
  TrueSym : TItem;
const
  whitespace  = [#0..' '];
  stopchars   = whitespace + ['(',')','[',']','{','}', '"', ''''];
  commentChar = '#';
  prompt0     = 'imp> ';
  prompt1     = '...> ';

var
  line   : string;
  lx, ly : cardinal;
  done   : boolean = false;

function k2s( kind :  TKind ) : string;
  begin
    case kind of
      kNUL : result := 'NUL';
      kCEL : result := 'CEL';
      kERR : result := 'ERR';
      kINT : result := 'INT';
      kSTR : result := 'STR';
    end
  end;

var debugging : boolean = true;
procedure debug( msg : string ); inline;
  begin
    if debugging then writeln( msg )
  end;

procedure error( const err: string );
  begin
    write( 'error at line ', ly, ', column ', lx, ': ' );
    writeln( err );
    halt;
  end; { error }

function Depth : cardinal;
  begin
    result := Length(nest);
  end;

function NextChar( var ch : char ) : char;
  procedure prompt;
    begin
      { write the prompt first, because eof() blocks. }
      if length(nest) > 0
        then write( nest, prompt1 )
        else write( prompt0 );
      if eof then begin
        ch := ascii.EOT;
        line := ch;
        done := true;
        if depth > 0 then error( 'unexpected end of file' );
        writeln;
        halt; { todo : remove this once depth-checking works correctly }
      end else begin
        readln( line );
        line := line + ascii.LF; { so we can do proper lookahead. }
        inc( ly );
        lx := 0;
      end
    end;
  begin
    while lx + 1 > length( line ) do prompt;
    inc( lx );
    ch := line[ lx ];
    // debug( '[ line ' + n2s( ly ) +
    //        ', column ' + n2s( lx ) + ' : ' +  ch + ']' );
    result := ch;
  end; { NextChar( ch ) }

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
    while result and (i <= length(s)) do begin
      if s[i] in ['0'..'9'] then num := num * 10 + ord(s[i]) - ord('0')
      else result := false;
      Inc(i);
    end;
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
    if last = 0 then ch := #0 else ch := s[ last ];
    SetLength( s, last - 1 );
    result := ch;
  end;

function ReadString : TItem;
  var s : string = '';
  begin
    AppendStr(nest, '"');
    while NextChar(ch) <> '"' do
      if ch = '\' then
        case NextChar(ch) of
          '0' : s := s + #0;
          't' : s := s + ^I;
          'n' : s := s + LineEnding;
          else s := s + ch;
        end
      else s := s + ch;
    PopChar(nest); NextChar(ch);
    result := Item(kSTR, Sym(s))
  end;

procedure SkipCommentsAndWhitespace;
  begin
    while ch in whitespace do
      if NextChar(ch) = commentChar then
        repeat until NextChar(ch) = ascii.LF
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
      if ch = expect then result := NullSym
      else result := Item(kERR, Sym('List end mismatch. Expected: '
                         + expect + ', got: ' + ch));
    end;
    NextChar(ch);
  end; { ReadListEnd }

function ShowItem(item :TItem) : string; Forward;
function ReadNext( out value : TItem ): TItem;

  function ReadList( out res : TItem; AtHead : boolean) : TItem;
    var car, cdr : TItem;
    begin
      if AtHead then begin nest += ch; NextChar(ch) end;
      SkipCommentsAndWhitespace;
      if (ch in [')', ']', '}']) then
        begin
          res := NullSym; NextChar(ch);
        end
      else if ReadNext(car).kind = kERR then res := car
      else if ReadList(cdr, false).kind = kERR then res := cdr
      else res := Cons(car, cdr);
      if AtHead then PopChar(nest);
      result := res;
      // debug('List -> ' + k2s(res.kind) + ' : ' + ShowItem(res));
    end; { ReadList }

  function ReadQuote : TItem;
    begin
      NextChar(ch);
      if ReadNext(result).kind <> kERR
        then result := Cons(Item(kSym, Sym('quote')), result)
    end; { ReadQuote }

  begin
    SkipCommentsAndWhitespace;
    case ch of
      '(','[','{' : ReadList(result, true);
      ')',']','}' : result := ReadListEnd;
      '"'         : result := ReadString;
      ''''        : result := ReadQuote;
      else result := ReadAtom;
    end;
    value := result;
  end; { ReadNext }

function Eval( item : TItem ) : TItem;
  begin
    result := item
  end;

function DumpCell( ref : TItem ): string;
  var cell : TCell;
  begin
    cell := cels[ ref.data ];
    result :=
      'Cons(' +
      k2s(cell.car.kind) + ':' + n2s(cell.car.data) + ',' +
      k2s(cell.cdr.kind) + ':' + n2s(cell.cdr.data) + '):' +
      n2s(ref.data);
  end; { DumpCell }

function ShowItem( item : TItem ) : string;

  function ShowList( ref : TItem; AtHead : boolean) : string;
    var cell : TCell;
    begin
      // debug('ShowList:' + DumpCell(ref));
      if AtHead then result := '(' else result := ' ';
      cell := cels[ ref.data ];
      result += ShowItem( cell.car );
      case cell.cdr.kind of
        kNUL : AppendStr( result, ')' );
        kCEL : AppendStr( result, ShowList( cell.cdr, false ));
        else   AppendStr( result, ' . ' + ShowItem( cell.cdr ) + ')');
      end;
    end; { ShowList }

  begin
    case item.kind of
      KNUL,
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
  NullSym := Item(kNUL, Sym('()'));
  TrueSym := Item(kSYM, Sym('T'));
  repeat Print(Eval(ReadNext(val)))
  until (val.kind = kERR)
end.
