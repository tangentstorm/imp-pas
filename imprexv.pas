{ imprexv : implish parser expression virtual machine }
{$mode delphi}
unit imprexv;
interface

type
  TCharGen = function : char;
  TCharSet = set of char;
  TRule	   = cardinal;

//-- primitive rule constructors -------------------------------

// nul : matches the empty string. (always matches)
function nul : TRule;

// eoi : matches the end of input.
function eoi : TRule;

// any : matches any single character in the given set.
function any( s : TCharSet ) : TRule;

// lit : matches a literal string.
// As a convenience when using the combinators below,
// you can also just pass the raw string.
function lit( s : string ) : TRule;

//-- combinators -----------------------------------------------

// alt : attempts to match each rule, in order from left to right.
// Succeeds if and only if at least one of the sub-rules succeeds.
// This is like separating sub-patterns by '|' in a regular expression.
// The name is short for "alternative".
function alt( rules : array of const ) : TRule;

// seq : match a specific sequence of rules, in order.
// Succeeds if and only if all of the sub-rules succeed.
//
// As a convenience, the remaining constructrors each take
// an 'array of const'. These are implicitly converted
// into a sequence, so most likely, the only time you really
// need to use 'seq' directly is inside an 'alt' constructor.
function seq( rules : array of const ) : TRule;

// rep : matches a rule repeatedly.
// This is the 'kleene plus' from formal language theory.
// It works like like the '+' character in a regular expression.
function rep( rules : array of const ) : TRule;

// neg : negate a match rule.
// This implements a logical 'not' operator: if the underlying
// pattern succeeds, then this rule will fail, and vice versa.
function rep( rules : array of const ) : TRule;

// opt : optionally match a rule. Always succeeds.
// This works like the '?' character in a regular expression.
// opt([x,y,z]) is the same as alt(seq([x,y,z]), nul)
function opt( rules : array of const ) : TRule;

// orp : optionally repeat a sequence of rules. Always succeeds.
// This is the 'kleene star' from formal language theory.
// It works like the '*' character in a regular expression.
// orp([x,y,z]) is the same as opt(rep([x,y,z]))
function orp( rules : array of const ) : TRule;

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
function def( name : string; rules : array of const ) : TRule;

// sub : invoke a named rule.
// To allow mutually recursive rules, a name can be referenced
// before it has been defined.
function sub( name : string ) : TRule;

//-- action and event system -----------------------------------

// act : trigger a particular action when a rule matches.
//
// This is the most primitive mechanism for triggering
// behavior when a match succeeds. This is used internally,
// and can be used to create new generic action rules (like
// the tree-building rules in the next section).
function act( action : cardinal; rules : array of const ) : TRule;

// TODO : evt : trigger a callback before and after a match.
// These could be used either to trigger immediate actions, or
// as predicates to control the flow of grammar.
//
// function evt( e : TTokenCallback; rules : array of const ) : TRule;
// procedure hook( e : TTokenCallback );

//-- token trees -----------------------------------------------

// These first few routines create named rules (just like 'def'),
// but in addition, allow creation of token streams and abstract
// syntax trees.

// tok : define a rule that generates a token when matched.
function tok( name : string; rules : array of const ) : TRule;

// skip : this is exactly the same as 'token', except that the
// generated token will be marked as hidden. This is intended
// for matching comments and whitespace.
function skip( name : string; rules : array of const ) : TRule;

// node : define a rule that generates a node in the abstract
// syntax tree when matched. 
function node( name : string; rules : array of const ) : TRule;

// These next rules alter the tree-building process in various
// ways, or allow re-arranging the tree.

// hide : match a sequence of rules, but do not include them in
// the generated tree. This like the '!' operator in ANTLR 3.
function hide(rules : array of const) : TRule;

// lift : promote the matched sequence to the head of the
// current node. This is like the '^' operator in ANTLR 3.
// It is useful for things like moving infix operators to the
// start of the list. Generally you would only apply this to
// a single token, but you can promote a whole sequence if
// you really want.
function lift(rules : array of const) : TRule;

// virt : emit a virtual token of length 0. Always succeeds.
function virt( name : string ) : TRule;

implementation

begin
end.
