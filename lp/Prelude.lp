require open Logic.U.Set;

symbol {|eo::typeof|} : Π [S : Set], (El S → Set);
rule {|eo::typeof|} [$S] $x ↪ $S;

symbol Bool : Set;
injective symbol Proof : El Bool → Set;
