# TableGen MIR Patterns - Design log

## Milestones/TODOs

TODO Next:
  - Look at replacing more patterns
  - Look into adding a Pattern Binder to do more binding earlier and not at codegen time.
    - It would try to bind a "match" and "apply" pattern together, checking consistency between patterns (e.g. if a register is present in both, check the types are equal) 
  - Match register equality (important for proper matching)

TODO Later:
  - Cleanup unused MatchDatas that are generated somehow
  - Look into leveraging MatchDAG more.
  - Figure out a better system for G_CONSTANT & co. Apply Gen.
  - Match commutable instructions (important for proper matching)
    - May be complex with current system.
    - Blocker: how to keep track of what was matched and where? How to know which ID to use to fetch the operands? MatchInfo may need to become smarter/more complex.
  - Move more rules to MIR and see if it breaks even more

## Syntax

The actual syntax of the patterns should be very close to MIR's, but I believe it should be somewhat separate and not forced to share a parser in the first iteration of the system. Unifying the parsers cleanly later should be possible though.

The idea is to start with a dumbed-down version of MIR patterns. The grammar in a EBNF-like syntax would be (* = 0 or more, + = 1 or more)
```
reg         := '%' (identifier | integer) (':' ('(' LLT ')'))?
immtype     := 'i' integer | 'f32' | 'f64'
imm         := immtype ('+' | '-') (integer | floating-point-number)
op          := reg | imm | '_'
inst-set    := '(' identifier ('|' identifier)+ ')'
reg-list    := reg (',' reg)*
op-list     := op (',' op)*
inst        := (reg-list '=')? (inst-name | inst-set) op-list?
```

This very small syntax can be easily parsed by recursive descent with some basic string manipulation functions.

Notes:
 - No support for physical registers (`$`) at first. They're not really present in most cases and since we're targeting gMIR, they're not needed. We can always add them later if we want to.
 - We support using multiple instruction names together. e.g. if we want to match both G_PTR_ADD and G_ADD we can use `%0(s32) = (G_PTR_ADD | G_ADD) %1, %2`
 - '_' is a wildcard operand. It means the pattern does not care about the operand.

TODO:
  - Support vector/pointer types
  - Support other types of macros, like !implicit_def and !constant for operands.
  - Support matching & reusing operands that aren't registers.
    - Currently, using something like `G_AND %x, %y` constraints x/y to be registers. They don't have to, we could add a way to specify that this can be an immediate as well?
  - Support matching variadic number of operands/elements.
    - For now we don't handle variadic-ness beyond semantic checking. Need to figure out a syntax   +  system to express, match and generate variadic operands. Current idea would be to do something like C++ with "packed operands".

### TableGen 

I prefer to not spend too much time on this as I see syntax as a low-level issue.
It can always be tweaked during review. For now, it's simply a string of code.
Context determines if this is MIR or C++ code, e.g. for combines we use GIMIRCombineRule.

``` 
[{MIR
    %1(s32) = G_AND %A, %MASK
    %root = G_TRUNC %1
}]
```

Another option which may be simpler is to add a DAG operator like this:
``` 
(mir "%root = G_TRUNC _")
(mir [{
  %1(s32) = G_AND %A, %MASK
  %root = G_TRUNC %1
}])
``` 

### Other considerations

We could also simply integrate MIR more closely with the existing DAG stuff.
``` 
(G_TRUNC (G_AND %A, %MASK))
```

This would be simpler to undertake but I don't think it's a good idea to force the use of an "unfit" syntax to represent MIR. DAGs and MIR are different, and some problems would likely arise:
 - How would we constrain the RegClass/RegBank of a given register?
 - How would we cleanly handle multiple return values, or no return values at all for an instruction?
 - What if some features added for the DAG pats interfere/breaks MIR patterns?

## Type Inference/Semantic Analysis

TODO:

Some cases may be annoying to handle with MIR Patterns as-is. An example
would be creating a new intermediate instruction. Take a sample pattern:
```
%a = G_XOR %b, %c
%root = G_AND %a, %d
->
%foo = G_AND %d, %b
%root = G_XOR %foo, %c 
``` 

If we want to match this on any type, we need a way to say "%foo can have the same type as %a". This could be implemented with an additional RegEq constraint in TypeConstraint. Syntax could be `%foo:(%a) = ...` for instance.

## MIR Parsing

The current implementation uses a custom, very simple parser.
The rationale for this is:
- MIRParser is vastly more complex than what we need. Making it fit here would probably be a huge headache and equal to bikeshedding IMO.
- MIR is syntactically simple enough. We probably won't be making crazy patterns from the start so doing trivial parsing should be easy enough.
- Merging the parsers later is possible given sufficient abstraction, but may not be needed at all. There is a chance that the MIR syntaxes diverge over time.
  - Representing BBs may not be needed at all in the MIR Patterns.
  - MIR Patterns may want more syntactic sugar to make pattern writing easier. e.g. calling some "MIRPatFrag" with templated arguments like `%0 = MyPatt<G_ADD, G_ADD> %1, %2, %3`.
  - MachineInstrs is not a good IR for what we want to do. We need more something akin to a graph to emit the patterns and perform things like inference.


## Pattern Roots

The root of a pattern determines the point from which we can start matching it.
It also determines the instruction to replace in a combine, for instance.

As MIR doesn't allow forward references, we can assume that the list of instructions is already topologically sorted. If we were to make a tree between
defs and uses in the instruction, its root would always be the last instruction
in the pattern if the pattern is well formed.

TODO: Canonicalize the ordering of instructions?

## Integration with existing TableGen Backends

The idea is to make this as easy to integrate for other backends that may not handle these new patterns. An example would be the DAGISel emitter that doesn't need to reason about MIR. For those, they should just ignore rules using MIR or error-out.

Initial testing will be done on the Combiner to try and replace match/apply functions.

### GICombinerEmitter

As much as I'd like to make the patterns rely on the information in the MIR, there are a lot of changes that would be needed to the GICombinerEmitter to make pure MIR patterns fit with its current system. Thus for now I just added special-casing for code blocks that start with MIR.

#### Initial/Easy integration
 - Generate C++ code based on the pattern and let it emit it like it would emit a C++ code snippet. Cleanly fits in the current architecture that way I think. Tighter integration can be done later.


## Example 

### Example of Converted Combine Rules

#### undef_to_int_zero

DAG/C++:
``` 
def undef_to_int_zero: GICombineRule<
  (defs root:$root),
  (match (wip_match_opcode G_AND, G_MUL):$root,
         [{ return Helper.matchAnyExplicitUseIsUndef(*${root}); }]),
  (apply [{ Helper.replaceInstWithConstant(*${root}, 0); }])>;
```

MIRPat
```
def mirpat_undef_to_int_zero: GIMIRCombineRule<
  [{
    %imp = G_IMPLICIT_DEF
    %root = (G_AND | G_MUL) _, %imp
  }],
  [{MIR
    %root = G_CONSTANT 0
  }]>;
```

Note that this pattern is interesting because G_AND/G_MUL are commutable.
This means that this should also match with the implicit def in the first place.
