{ imprex : implish parser expressions  }
{$mode delphi}
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

// Rules themselves are variable length records. They consist
// of a cardinal representing the TCode, plus any data specific
// to that type. For example, 'alt' and 'seq' each require a
// length for tracking the number of sub-rules, whereas 'lit'
// and 'any' records reference the lookup tables. All of these
// things are just cardinals, though, so 'rultbl' is just a big
// array of cardinal pairs.
type
  TRuleData = record
		code, data : cardinal
	      end;
var
  rultbl : GArray<TRuleData>;

// The 'strtbl' and 'chstbl' arrays are simple lookup tables
// for strings and character sets, respectively.
  strtbl : GArray<string>;
  chstbl : GArray<TCharSet>;

// 'deftbl' maps rule names (strings) to definitions in 'rultbl'.
// When a named rule is referenced before it is defined, the 'rule'
// field will be zero.
type
  TRuleName = record
		name : string;
		rule : TRuleID;
	      end;
var
  deftbl : GArray<TRuleName>;

//-- constructors -------------------------------------

function nul;
  begin
  end;

function eoi : TRuleID;
  begin
  end;

function any( s : TCharSet ) : TRuleID;
  begin
  end;

function lit( s : string ) : TRuleID;
  begin
  end;

function alt( rules : array of const ) : TRuleID;
  begin
  end;

function seq( rules : array of const ) : TRuleID;
  begin
  end;

function rep( rules : array of const ) : TRuleID;
  begin
  end;

function neg( rules : array of const ) : TRuleID;
  begin
  end;

function opt( rules : array of const ) : TRuleID;
  begin
  end;

function orp( rules : array of const ) : TRuleID;
  begin
  end;

function def( name : string; rules : array of const ) : TRuleID;
  begin
  end;

function sub( name : string ) : TRuleID;
  begin
  end;

function act( action : cardinal; rules : array of const ) : TRuleID;
  begin
  end;

function tok( name : string; rules : array of const ) : TRuleID;
  begin
  end;

function skip( name : string; rules : array of const ) : TRuleID;
  begin
  end;

function node( name : string; rules : array of const ) : TRuleID;
  begin
  end;

function hide(rules : array of const) : TRuleID;
  begin
  end;

function lift(rules : array of const) : TRuleID;
  begin
  end;

function virt( name : string ) : TRuleID;
  begin
  end;

begin
end.
