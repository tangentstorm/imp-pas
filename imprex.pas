{ imprex : implish parser expressions  }
{$mode objfpc}{$h+}
unit imprex;
interface uses arrays;

type
  TCharGen = function : char;
  TCharSet = set of char;
  TRuleID	   = cardinal;

//-- primitive rule constructors -------------------------------

// nul : matches the empty string. (always matches)
function nul : TRuleID;

// eoi : matches the end of input.
function eoi : TRuleID;

// any : matches any single character in the given set.
function any( s : TCharSet ) : TRuleID;

// lit : matches a literal string.
// As a convenience when using the combinators below,
// you can also just pass the raw string.
function lit( s : string ) : TRuleID;

//-- combinators -----------------------------------------------

// alt : attempts to match each rule, in order from left to right.
// Succeeds if and only if at least one of the sub-rules succeeds.
// This is like separating sub-patterns by '|' in a regular expression.
// The name is short for "alternative".
function alt( rules : array of const ) : TRuleID;

// seq : match a specific sequence of rules, in order.
// Succeeds if and only if all of the sub-rules succeed.
//
// As a convenience, the remaining constructrors each take
// an 'array of const'. These are implicitly converted
// into a sequence, so most likely, the only time you really
// need to use 'seq' directly is inside an 'alt' constructor.
function seq( rules : array of const ) : TRuleID;

// rep : matches a rule repeatedly.
// This is the 'kleene plus' from formal language theory.
// It works like like the '+' character in a regular expression.
function rep( rules : array of const ) : TRuleID;

// neg : negate a match rule.
// This implements a logical 'not' operator: if the underlying
// pattern succeeds, then this rule will fail, and vice versa.
function neg( rules : array of const ) : TRuleID;

// opt : optionally match a rule. Always succeeds.
// This works like the '?' character in a regular expression.
// opt([x,y,z]) is the same as alt(seq([x,y,z]), nul)
function opt( rules : array of const ) : TRuleID;

// orp : optionally repeat a sequence of rules. Always succeeds.
// This is the 'kleene star' from formal language theory.
// It works like the '*' character in a regular expression.
// orp([x,y,z]) is the same as opt(rep([x,y,z]))
function orp( rules : array of const ) : TRuleID;

//-- named rules -----------------------------------------------

// Names allow you to re-use patterns that appear in multiple
// places.
//
// More importantly, they allow you to define recursive
// languages ('context free grammars' in formal language
// theory.
//
// For example, in pascal, you can use a repeat statement
// inside a case statement inside a repeat statement, etc.
// You could handle this with something like:
//
//  def('stmt', [ alt([ sub('case'), sub('repeat')]) ]);
//  def('block', [ sub('stmt'), orp([';', sub('stmt')]) ]);
//  tag('repeat', [ 'repeat', sub('block'),
//                  'until', sub('expression') ]);
// ... etc.

// def : define a named rule.
function def( name : string; rules : array of const ) : TRuleID;

// sub : invoke a named rule.
// To allow mutually recursive rules, a name can be referenced
// before it has been defined.
function sub( name : string ) : TRuleID;

//-- action and event system -----------------------------------

// act : trigger a particular action when a rule matches.
//
// This is the most primitive mechanism for triggering
// behavior when a match succeeds. This is used internally,
// and can be used to create new generic action rules (like
// the tree-building rules in the next section).
function act( action : cardinal; rules : array of const ) : TRuleID;

// TODO : evt : trigger a callback before and after a match.
// These could be used either to trigger immediate actions, or
// as predicates to control the flow of grammar.
//
// function evt( e : TTokenCallback; rules : array of const ) : TRuleID;
// procedure hook( e : TTokenCallback );

//-- token trees -----------------------------------------------

// These first few routines create named rules (just like 'def'),
// but in addition, allow creation of token streams and abstract
// syntax trees.

// tok : define a rule that generates a token when matched.
function tok( name : string; rules : array of const ) : TRuleID;

// skip : this is exactly the same as 'token', except that the
// generated token will be marked as hidden. This is intended
// for matching comments and whitespace.
function skip( name : string; rules : array of const ) : TRuleID;

// node : define a rule that generates a node in the abstract
// syntax tree when matched.
function node( name : string; rules : array of const ) : TRuleID;

// These next rules alter the tree-building process in various
// ways, or allow re-arranging the tree.

// hide : match a sequence of rules, but do not include them in
// the generated tree. This like the '!' operator in ANTLR 3.
function hide(rules : array of const) : TRuleID;

// lift : promote the matched sequence to the head of the
// current node. This is like the '^' operator in ANTLR 3.
// It is useful for things like moving infix operators to the
// start of the list. Generally you would only apply this to
// a single token, but you can promote a whole sequence if
// you really want.
function lift(rules : array of const) : TRuleID;

// virt : emit a virtual token of length 0. Always succeeds.
function virt( name : string ) : TRuleID;

//////////////////////////////////////////////////////////////
implementation
//////////////////////////////////////////////////////////////

//-- rule database -------------------------------------

// The rules are stored in a simple in-memory semi-relational
// database. The tables are just dynamic arrays, and the
// primary key for a record is simply its index within the array.

// Rule codes (corresponding to the public constructors) are
// stored as cardinals in the database to allow creating
// custom actions later (even at runtime). For the predefined
// types, however, can cast the cardinal to a TCode:
type
  TCode	= (kNul, kEoi, kAny, kLit, kAlt, kSeq, kRep,
	   kNeg, kOpt, kOrp, kDef, kSub, kAct, kTok,
	   kSkip, kNode, kHide, kLift, kVirt,
	   kCustom);

// Rules are stored as pairs of cardinals. The first number
// represents the rule code (either the ord() of one of the
// above values, or a custom code). The second number either
// contains a constant or the key of a value in another table.
type
  TRuleData = record
		code, data : cardinal
	      end;
function RuleData(code, data : cardinal) : TRuleData;
  begin
    result.code := code;
    result.data := data;
  end;

operator = (a : TRuleData; b : TRuleData) : boolean;
  begin
    result := (a.code = b.code) and (a.data = b.data)
  end;

// sadly, despite doing the above, trying to use GEqArray below
// results in an error:
// Error: Operator is not overloaded: "TRuleData" = "TRuleData"
var
  rultbl : specialize GArray<TRuleData>;

// The 'strtbl' and 'settbl' arrays are simple lookup tables
// for strings and character sets, respectively.
  strtbl : specialize GEqArray<string>;
  settbl : specialize GEqArray<TCharSet>;

// 'argtbl' stores arguments. generally these are the arrays for
// alt and the various sequence operators, but really it can be
// any kind of data.
type
  TRuleArgs = array of cardinal;
var
  argtbl : specialize GEqArray<TRuleArgs>;

// 'deftbl' maps rule names (strings) to definitions in 'rultbl'.
// When a named rule is referenced before it is defined, the 'rule'
// field will be zero.
type
  TRuleName = record
		name : string;
		rule : TRuleID;
	      end;
var
  deftbl : specialize GArray<TRuleName>;

//-- constructors -------------------------------------

function nul : TRuleID;
  begin
    result := 0  { there's only one nul rule }
  end;

function eoi : TRuleID;
  begin
    result := 1  { there's only one end of input rule }
  end;

function any( s : TCharSet ) : TRuleID;
  var id : cardinal;
  begin
    if not settbl.Find( s, id ) then id := settbl.Append( s );
    result := rultbl.Append( RuleData( ord( kAny ), id ));
  end;

function lit( s : string ) : TRuleID;
  var id : cardinal;
  begin
    if not strtbl.Find( s, id ) then id := strtbl.Append( s );
    result := rultbl.Append( RuleData( ord( kLit ), id ));
  end;

function compile( code : TCode; rules : array of const ) : TRuleID;
  var i : cardinal; args : TRuleArgs;
  begin
    SetLength( args, Length( rules ));
    for i := 0 to high( rules ) do begin
      case rules[i].vtype of
	vtString     : args[i] := lit(rules[i].vstring^);
	vtAnsiString : args[i] := lit(AnsiString(rules[i].vAnsiString));
      end
    end;
    i := argtbl.Append( args );
    result := rultbl.Append( RuleData( ord( code ), i ));
  end;

function alt( rules : array of const ) : TRuleID;
  begin
    result := compile(kAlt, rules)
  end;

function seq( rules : array of const ) : TRuleID;
  begin
    result := compile(kSeq, rules)
  end;

function rep( rules : array of const ) : TRuleID;
  begin
    result := compile(kRep, rules)
  end;

function neg( rules : array of const ) : TRuleID;
  begin
    result := compile(kNeg, rules)
  end;

function opt( rules : array of const ) : TRuleID;
  begin
    result := compile(kOpt, rules)
  end;

function orp( rules : array of const ) : TRuleID;
  begin
    result := compile(kOrp, rules)
  end;

function def( name : string; rules : array of const ) : TRuleID;
  begin
    // TODO: record the name
    result := compile(kDef, rules)
  end;

function sub( name : string ) : TRuleID;
  begin
    // TODO: retrieve the rule by name
  end;

function act( action : cardinal; rules : array of const ) : TRuleID;
  begin
    // TODO: record the action
    result := compile(kAct, rules)
  end;

function tok( name : string; rules : array of const ) : TRuleID;
  begin
    // TODO: record the name
    result := compile(kTok, rules)
  end;

function skip( name : string; rules : array of const ) : TRuleID;
  begin
    // TODO: record the name
    result := compile(kSkip, rules)
  end;

function node( name : string; rules : array of const ) : TRuleID;
  begin
    // TODO: record the name
    result := compile(kNode, rules)
  end;

function hide(rules : array of const) : TRuleID;
  begin
    result := compile(kHide, rules)
  end;

function lift(rules : array of const) : TRuleID;
  begin
    result := compile(kLift, rules)
  end;

function virt( name : string ) : TRuleID;
  begin
    // TODO: record the virtual token
  end;

begin
end.
