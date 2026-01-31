#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "template.typ": *

// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.
#show: project.with(
  title: [
    Category Theory

    take home test

    2026
  ],
  authors: (),
)

I have written Q1-4, and formally verified them in @lean.
Below I have tried to rewrite these lean proofs into natural langauge proofs.

#outline()

#pagebreak()

= Question 1

#link("https://live.lean-lang.org/#codez=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")[Link to a live lean version here]

The left adjoint of the functor $R ^ ((-)) : C^"op" -> C$,
is the functor is $R' ^ ((-)) : C -> C^"op"$,
given by $R'^(X) eq.delta R^X$,
and $R'^(f) eq.delta "cur" ("app" compose (f times_m id))$.
As CCCs can get quite messy to work with I decided to leave it to the lean formalization.

#pagebreak()

= Question 2

#link("https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0BhFAUwHNoBPAFVUPJwE0IA7QgEyQChRJZEUNt8RUlErVaBGCXEpBsQgGdgSRnnQR5rduwhhCjOBKkiqNEVoCujYADdCUDXHNbrSKEqzpCcAN544ALjgKMl1HAF84AG0AZRAkdHRDYTIDAF0tFkIAMzgACQC4AAo/QBNKIJCvcwBKODLiuEAkwnLQ6rgAd2ooQnY4OAgsACsAgF44ADFLAGMYaBx+gZ64OLARuAA5FAooZXkcJDAwDOy8gBkC+qbglpq60ubKmo67bt75uAANVe9F18G4ADVVoBi4DgAFUADRFUFwQBv5ACagB1j5gn5LfZwHL+UZZSxwQAX5BClpCAB6AS/I4MMAHz4wkgOCAayIMSTSYswotlj5PnQIpjRt9er19itAViMbiCZCQMyKdSJUSMXAAPpwMmso45XIAJXOfkuFUcNyKdyuD3anRefT+n1F/IFbxFo0K0MCeBqTUKgLhoLdyNBqI5OQgYKWqyD0MKOUZICqat6HO8XJ5X1RQoBfWDdNFOWVhTDSxjvTZnEY8hgykmXkCuTOgGKiPJG1au1Y4EAAawA8llQVYYHgIJZgPBbb0B/AbajBQdkYDrKs8f9IYBWDcAm/tKyHWFkCuBsreTfs95Nbycra18icC1N0OCz0XvFvo6w4ABMOAAjNfn8/z71GChzNtMBgFJoUBXk4CwMhvwFQhiXgawoN6SZ4kmBCBTvDlCkfF930ZLIaiwr8jyIgVHXQh8cHkRgWDfBkPnvFY8I/SjqKfXpRQguAoDaKIJkYaZZmWRU93AdJiKPZVRjIhiiikpiqJox9mOfGoBVFKAsnQc8dyPX8YH/eJB2AtMwIgqCYPgT5UCgpD0BQsTegjPYp1QHAslLWj/nouAXKU18ah8+Sn1Q3pHVBLyAuonCMSck9/IowLVg4rioiyHBdP0wCyFEgVtN6TwshgRUYDcZRiE8RLIKI8zgxnc9JlQUqvCdRV3xdREoRa2F4TgJFoVBTqUGvOrkKgwo8UfNyYEhQoVw/SbaMU+TX3XeKWKqclAma1qDHarauv+dq+pagt7NGcbXNLabFsilalKfdaKs47jIiSWhgBYISIBEqCJOvVZ1M0rc3GIVBCuKpRGDKytRg489qsBaF4KI+rGoBOY/mhQakaPGy7OIzyMNm70hvsik4Fmj10aGYmbxhlJksiAn9kVd7sqI37Z1JtjRgBtVi1LctK3repRSbOstRGRYWw7Lsez7UcfFRBXxyI1NT0VsTLz+6FM0kry6Wxoj0oAwyaoVdjKvs6qIFQnFmFg4NDeIlHIaa2TIzojlrBqIM9Ywj3vb6VCGakz7vqI3KBWNgygLNkzLaqh3PmJKC7eqq8QGshrXaKVK1Y8/WamJMmnX12i86nOgi6ghnUujzK2e3VE92Vs9VanT5AVQVZu8BGbV0VE7C1RfKwZKyHyotuGHYRkmcez4gvCZlZ+7BfCS4pzy3m9fDzwZ5eWZYRvgdBorx6hirp/gEC563NOk6WOqF68WdPkKOlGVm94alGV/H6Ihmr0RA4GEmAQ+2UixAA")[Link to a live lean version here]

This task was solved much better in lean and I recommend looking at it there more.

We begin by constructing $H_l, H_r : "Set"^("obj"(C)) -> "Set"^C$,
which will be the adjoints of $H$.
$
H_l (X)(V) & eq.delta sum_(U : C) C(U, V) times X U \
H_l (X)(f)(chevron.l U, m, x, chevron.r) & eq.delta chevron.l U, f compose m, x, chevron.r \
H_l (f)_V (chevron.l U, m, x, chevron.r) & eq.delta chevron.l U, m, f x, chevron.r \
\ \ \ \
H_r (X)(V) & eq.delta product_(U : C) C(V, U) -> X U \
H_r (X)(f)(o)(U)(m) & eq.delta o" "U (m compose f) \
H_r (f)_V (o)(U)(m) & eq.delta f (o U m) $

The functorality of
$H_l$, $H_r$, $H_l (X)$ and $H_r (Y)$;
and the naturality of $H_l (f)$ and $H_r (f)$
follow definitionally.

== Functoriality Proofs

These proofs were auto-solved in the Lean formalization,
but I include them here anyway.

=== $H_l (X)$ is functorial

*Identity*:
$
H_l (X)(id_V)(chevron.l U, m, x chevron.r)
& = chevron.l U, id_V compose m, x chevron.r \
& = chevron.l U, m, x chevron.r
$

*Composition*:
$
H_l (X)(g compose f)(chevron.l U, m, x chevron.r)
& = chevron.l U, (g compose f) compose m, x chevron.r \
& = chevron.l U, g compose (f compose m), x chevron.r \
& = H_l (X)(g)(chevron.l U, f compose m, x chevron.r) \
& = H_l (X)(g)(H_l (X)(f)(chevron.l U, m, x chevron.r))
$

=== $H_l$ is functorial

*Identity*:
$
(H_l (id_X)) (chevron.l U, m, x chevron.r)
& = chevron.l U, m, id_X (x) chevron.r \
& = chevron.l U, m, x chevron.r
$

*Composition*:
$
(H_l (g compose f)) (chevron.l U, m, x chevron.r)
& = chevron.l U, m, (g compose f)(x) chevron.r \
& = chevron.l U, m, g(f(x)) chevron.r \
& = (H_l (g)) (chevron.l U, m, f(x) chevron.r) \
& = (H_l (g)) ((H_l (f)) (chevron.l U, m, x chevron.r))
$

=== $H_r (X)$ is functorial

*Identity*:
$
H_r (X)(id_V)(o)(U)(m)
& = o" "U (m compose id_V) \
& = o" "U (m)
$

*Composition*:
$
H_r (X)(g compose f)(o)(U)(m)
& = o" "U (m compose (g compose f)) \
& = o" "U ((m compose g) compose f) \
& = H_r (X)(f)(o)(U)(m compose g) \
& = H_r (X)(f)(H_r (X)(g)(o))(U)(m)
$

=== $H_r$ is functorial

*Identity*:
$
(H_r (id_X)) (o)(U)(m)
& = id_X (o" "U m) \
& = o" "U m
$

*Composition*:
$
(H_r (g compose f)) (o)(U)(m)
& = (g compose f)(o" "U m) \
& = g(f(o" "U m)) \
& = (H_r (g)) ((H_r (f)) (o))(U)(m)
$

== Naturality Proofs

Likewise here

=== $H_l (f)$ is natural

*RTP*: $H_l (Y)(g) compose H_l (f)_V = H_l (f)_W compose H_l (X)(g)$

$
(H_l (Y)(g) compose H_l (f)_V)(chevron.l U, m, x chevron.r)
& = H_l (Y)(g)(chevron.l U, m, f x chevron.r) \
& = chevron.l U, g compose m, f x chevron.r \
& = H_l (f)_W (chevron.l U, g compose m, x chevron.r) \
& = H_l (f)_W (H_l (X)(g)(chevron.l U, m, x chevron.r)) \
& = (H_l (f)_W compose H_l (X)(g))(chevron.l U, m, x chevron.r)
$

=== $H_r (f)$ is natural

*RTP*: $H_r (Y)(g) compose H_r (f)_V = H_r (f)_W compose H_r (X)(g)$

$
(H_r (Y)(g) compose H_r (f)_V)(o)(U)(m)
& = H_r (Y)(g)(H_r (f)_V (o))(U)(m) \
& = H_r (f)_V (o)(U)(m compose g) \
& = f(o" "U (m compose g)) \
& = H_r (f)_W (o" "U (m compose g)) \
& = H_r (f)_W (H_r (X)(g)(o)(U)(m)) \
& = (H_r (f)_W compose H_r (X)(g))(o)(U)(m)
$

== $H_l tack.l H$

We start by defining the unit $eta : id -> H H_l$ and the counit $epsilon : H_l H -> id$,
We pick
$eta_X (V) (v) eq.delta chevron.l V, id, v chevron.r$ and
$epsilon_(X,Y) (chevron.l V , f, o chevron.r) eq.delta X (f) o $.

=== $eta_X$ naturality in $X$

*RTP*: $H(H_l (f)) compose eta_X = eta_Y compose f$

$
(H(H_l (f)) compose eta_X)(V)(v)
& = H(H_l (f))(eta_X (V)(v)) \
& = H(H_l (f))(chevron.l V, id, v chevron.r) \
& = H_l (f)_V (chevron.l V, id, v chevron.r) \
& = chevron.l V, id, f V v chevron.r \
& = eta_Y (V)(f V v) \
& = (eta_Y compose f)(V)(v)
$

=== $epsilon_(X,Y)$ naturality in $X$

*RTP*: $f_V compose epsilon_(X, V) = epsilon_(Y, V) compose H_l (f)_V$ for $f : X -> Y$ natural transformation

$
(f_V compose epsilon_(X, V))(chevron.l U, m, x chevron.r)
& = f_V (X(m)(x)) \
& = (Y(m) compose f_U)(x) && "by naturality of" f \
& = Y(m)(f_U (x)) \
& = epsilon_(Y, V)(chevron.l U, m, f_U x chevron.r) \
& = (epsilon_(Y, V) compose H_l (f)_V)(chevron.l U, m, x chevron.r)
$

=== $epsilon_(X,Y)$ naturality in $Y$

*RTP*: $X(f) compose epsilon_(X, U) = epsilon_(X, V) compose H_l (X)(f)$ for $f : U -> V$

$
(X(f) compose epsilon_(X, U))(chevron.l W, m, x chevron.r)
& = X(f)(X(m)(x)) \
& = X(m compose f)(x) && "by functoriality of" X \
& = epsilon_(X, V)(chevron.l W, m compose f, x chevron.r) \
& = (epsilon_(X, V) compose H_l (X)(f))(chevron.l W, m, x chevron.r)
$

=== Left-triangle

*RTP*: $epsilon_(H_l (X), V) compose (H_l (eta_X))_V = id_(H_l (X)(V))$

$
(epsilon_(H_l (X), V) compose (H_l (eta_X))_V)(chevron.l U, m, x chevron.r)
& = epsilon_(H_l (X), V)(chevron.l U, m, eta_X (U)(x) chevron.r) \
& = epsilon_(H_l (X), V)(chevron.l U, m, chevron.l U, id, x chevron.r chevron.r) \
& = H_l (X)(m)(chevron.l U, id, x chevron.r) \
& = chevron.l U, m compose id, x chevron.r \
& = chevron.l U, m, x chevron.r
$

=== Right-triangle

*RTP*: $(H(epsilon_X))_U compose eta_(H(X), U) = id_(H(X)(U))$

$
((H(epsilon_X))_U compose eta_(H(X), U))(v)
& = H(epsilon_X)(eta_(H(X), U)(v)) \
& = epsilon_(X, U)(chevron.l U, id, v chevron.r) \
& = X(id)(v) \
& = v
$

== $H tack.l H_r$

We start by defining the unit $eta : id -> H_r H$ and the counit $epsilon : H H_r -> id$,
We pick
$eta_(X,Y) (v) (U) (m) eq.delta X (m) v$ and
$epsilon_X (V) (h) eq.delta h V id$.

Next We need to prove naturalities and the two triangle equalities.

The proofs for naturality and triangles are equally long and 
They are fully formalised in the lean proof.

// TODO: THIS IS JUST WRONG
//
// === $eta_(X,Y)$ naturality in $X$
//
// *RTP*: $H_r (V)(f) compose eta_(U,Y) = eta_(V,Y) compose H(f)$ for $f : U -> V$ natural transformation
//
// $
// (H_r (V)(f) compose eta_(U,Y))(x)(W)(m)
// & = H_r (V)(f)(eta_(U,Y)(x))(W)(m) \
// & = eta_(U,Y)(x)(W)(m compose f_W) \
// & = U(m compose f_W)(x) \
// & = (U(m) compose f_W)(x) && "by functoriality of" U \
// & = f_W (U(m)(x)) && "by naturality of" f \
// & = eta_(V,Y)(f_Y (x))(W)(m) \
// & = (eta_(V,Y) compose H(f))(x)(W)(m)
// $
//
// === $eta_(X,Y)$ naturality in $Y$
//
// *RTP*: $H_r (X)(f) compose eta_(X,U) = eta_(X,V) compose X(f)$ for $f : U -> V$ in $C$
//
// $
// (H_r (X)(f) compose eta_(X,U))(v)(W)(m)
// & = H_r (X)(f)(eta_(X,U)(v))(W)(m) \
// & = eta_(X,U)(v)(W)(m compose f) \
// & = X(m compose f)(v) \
// & = (X(m) compose X(f))(v) && "by functoriality of" X \
// & = X(m)(X(f)(v)) \
// & = eta_(X,V)(X(f)(v))(W)(m) \
// & = (eta_(X,V) compose X(f))(v)(W)(m)
// $
//
// === $epsilon_X$ naturality in $X$
//
// *RTP*: $f_V compose epsilon_X (V) = epsilon_Y (V) compose H(H_r (f))_V$ for $f : X -> Y$ natural transformation
//
// $
// (f_V compose epsilon_X (V))(h)
// & = f_V (h V id) \
// & = H_r (f)_V (h)(V)(id) \
// & = epsilon_Y (V)(H_r (f)_V (h)) \
// & = (epsilon_Y (V) compose H(H_r (f))_V)(h)
// $
//
// === Left-triangle
//
// *RTP*: $(H(epsilon_X))_U compose eta_(H(X), U) = id_(H(X)(U))$
//
// $
// ((H(epsilon_X))_U compose eta_(H(X), U))(v)
// & = H(epsilon_X)_U (eta_(H(X), U)(v)) \
// & = epsilon_X (U)(eta_(H(X), U)(v)) \
// & = eta_(H(X), U)(v)(U)(id) \
// & = H(X)(id)(v) \
// & = v
// $
//
// === Right-triangle
//
// *RTP*: $epsilon_(H_r (X), V) compose (H_r (eta_X))_V = id_(H_r (X)(V))$
//
// $
// ((H_r (epsilon_X))_V compose eta_(H_r (X), V))(h)(U)(m)
// & = H_r (epsilon_X)_V (eta_(H_r (X), V)(h))(U)(m) \
// & = eta_(H_r (X), V)(h)(U)(m)(U)(id) \
// & = H_r (X)(m)(h)(U)(id) \
// & = h U (id compose m) \
// & = h U m
// $

#pagebreak()

= Question 3

#link("https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0BhFAUwHNoBPAFVUPJwBlRgYBnHAZVSTENYsKhDAAdknQAoMQFchwAG79mhOJIkRuQuARglyVGlDITZSKMCRZ0SgN544ALjgUy3ZQF84AbS06DmgLpwABQAYvaacIAmlJoAlBLMMFCSAMYwklBKAILoxHAA7tTpYnBwGWF4RXCAjcBhwTgQWABWJXCAb+QlcQnJqekl2QASECBBpQBCYVk5wdF5BYQVqOM4pW0jSxWEAI41OCBccAuA1kRwq9UAvCU41UeoEgAmhABmvcQDIDhJg2AVxVYAGnAATTgAC1xtk4MFXN8gk8HBNXhC4P8AbFisVAjk4f1BoigcDUWisS8caF/qD8vw5sUFnZzg8cIc4MQGestrS4ElRElobVdmAYQy4EdmahpkdgZc4NDiudeXt6Yy5fyRUKQZL2VgyHBmKAvmi4AB9ODnEI7eWCo4Ay5ipmCjVaqC5TzMzYAGk0RFIBhwSGYzAgST80KN51+kqOCtVKvtcEdnnpbo92i9ZB9foDQbEwniSCESSUDm8KeG4KmM0pFQR7PhJIqwFuhvs5ys+ybcEArBuATf3De7Nm3NdrdVDih9wHA/oCQe4npjzjW3qP+aEZxIR58DfW4LDzgOdWOPPP3p8g8V6wbF1v+1q9/yD9iF8eKr7/UlLzGb55D4vM/cnsEAKr8oEshgpM0xEoiFKFMUpTsrU9RNLIazFNUcFmvySGVBIAACHg3kGaD6IQQwAWApRWAA8u4DghIBiIUdESzGhCdSNHAFFMbSFRQA84hiLh+FiIR0DERCgHVJR1FBKR9GMWcLF8ux6qnNxvGqOocAMIILBGCYZgWEoHh9L6ACSMgwGY6AlmBmZCBAeafJIMDmJYcC/m5EC5BoDgyaEgSAKVERoTBC0xtIFzyQbM8xtgFQWlnJrJtjxfGEAAHkg4CuUZpnmZZ1khQEDgmcwxUQEEsX5VMcnTFBVJwBATltoAF+TQoEwhMJZOAwGVtFLkE4UGtEQ0Mq60KatK+xIPIsaoMwYSBG1uWiF1PW+f1cVgcNjIVcFUzWsxXaNuynLoNy+r6otHXLd10l0X54W7UNqq3J5Gh7Tc53nSa7UWddPUPfFjE0juDpOh4P2dd156fEEL1eQVE3FCGzyvIKgSHTtgNXrGuSI59+ME4TaLg0t6AMoMBppfA6Pdpjm1BBDf3rRFVUnudHxCPEiQpNAE0AO0clyePogDYHhgzpMrbdfV0yFW3C2isroRLV1kzdvWIoNQOqhr91GlrkpE9jjoK0bZvmxbZseIACYSXb9aurXdhrDZsbOfcjSoq/bUu6872tHJ7st7dUn3ssleMe8rC2Mw70uIkHQ3+8zj37cbYNKtD4Bu+dkeKTTzuW4XhcxnGHhQLN2f6sjh1GkXdf1yX6fSDzUDoRutyV3AAtpUgKQzcwo3FIAl+QSEAA")[Link to a live lean version here]

To begin let us consider the $F$-algebra transformer
$accent(F, tilde) : F_"Alg" -> F_"Alg" eq.delta lambda chevron.l A, alpha chevron.r . chevron.l F (A), F (alpha) chevron.r$
on this we define the morphism $"down" : accent(F, tilde) I -> I eq.delta iota$,
which by definition satisfies the required equation.

// #figure(
//   diagram(cell-size: 15mm, $
//     F accent(F, tilde) 0 edge(F (0_alpha), ->) edge("d", accent(F, tilde) , ->) & F 0 \
//     accent(F, tilde) 0 slash ker(f) edge("ur", tilde(f), "~")
//   $)
// )

Now we can proceed to show that $iota$ is an isomorphism.

*Proof*:
- *RTP*: $exists m : C(I, F I), m compose iota = id_(F I) and iota compose m = id_(I)$
- *Use*: $([]_(accent(F, tilde) I))_h : C(I, F I)$
- *Case* : $iota compose ([]_(accent(F, tilde) I))_h = id_(F I)$
  - $
  iota compose ([]_(accent(F, tilde) I))_h 
  & = ("down" compose []_(accent(F, tilde) I))_h && "by definition" \
  & = ([]_(I))_h && "by composition of initial morphism" \
  & = (id_I)_h && "by uniqueness of initial morphism" \
  & = id_I && "by definition"
  $
- *Case* : $([]_(accent(F, tilde) I))_h compose iota = id_I$
  - $
  ([]_(accent(F, tilde) I))_h compose iota
  & = F (iota) compose F(([]_(accent(F, tilde) I))_h) && "by the homomorphism requirement on "iota \
  & = F (iota compose ([]_(accent(F, tilde) I))_h) && "by "F" functorality" \
  & = F (id_(F I)) && "by the previous case" \
  & = id_I  && "by "F" functorality" $

#pagebreak()

= Question 4

#link("https://live.lean-lang.org/#codez=JYWwDg9gTgLgBAWQIYwBYBtgCMB0BhFAUwHNoBPAFVUPJwQgDsJgATJdfdCAZ0JZwpkwhbgChREYQzgEYJclRpQy4yYWncAxmpaJGzNulnzl43ppjBG4gK4NgAN0JRecG6IdIowJFnSE4AG88OAAuOEFhAF84AG0AZRB2IyJSZRkAXXEWQgAzOCQWACsHOAAKADUwmThAE0oIoUIASmqyspD6yOa4AHWZFs7GuAB3aihCUTg4CCwiuAANMIBecu0yRj4kHBm5su2wBZwAJhbAdKI4CpbAN/JDgEZJuCSDwMWATRj86VCVtrWNthwT3K+zguWOTTOgAyCcqAVg3AJv7cAA+hC4IBrIjg0nRYPuoiQAA8rCA4JokAwYIisIQKRA0M4+EEquEOg1otV6ExWOxjGkyDg5AxuNAADJ5eBVQDFRHAAGJ2CzQHCaGxQZTbWblQolC5NcRMBjacA2GC+fxwYACo16gLhdkGLlcXi6dp1FndUZ0h6ae30xkrQIPKbeYioGAAQWKy2lspg8sVyt5OzgAB4AD4FYqlCr+tNzb7E0nkynU2njFgPKLidSliRSSN6yyMcoAURAlJYLDNxG1ojN3AtmgCZTA3mgwBgZAjtwADNPJy0malyHAAHIoEZjCZTAASECJ0iJualZoxcEAVYTSo8gB6sY+55ut9sMYg4ca5dBIj07g63lt8B9PmBQKSYgeF4Ph+AOAAK1QrvAgzCF2OT5Eu0GrnBARuuMDwJl8KyHtIDAPEC373h2fIQDKBGiOY9aUbq+pgIaxoBIhpoMBB4xBLuKEwDEZT5OEeGPKe574S0ZTANUgkMHOcAAPJgDR5SCSAc5LA8ZR4bwMA4HYjg4LkwDoHIUDlPkADtcArMAEI4J4HDRkKwC9jg1CFAA/OItLQIQRJmuxVIGUZziIoQACOnE3suKC8fxIlCWeUliRJAlHtJWYpQKhDabpDj6YZxmmXAFlWS0Vn5Kg1SAMBEcAOAANKCNWWaacC0tIwToEg3DcMAJIcJoqAQDwASoDEhDoK4gQxLmWAqFM3BgJg8CJgA3AAfHA4wMEgIBUhJ1ChQ8FmEHi8AEVMc2gAcjDoOOsSaVlgI+YigXGfV93aTtICIjl9UATYVKkiwb09g9n2It1j7+NGDBZOdxKML2UA2HKJkret3hklAEAba+WZHXiSAWKZOBmkUhAWI4AQpjIHVdT17AKgNQ3g8ImhwPtTQ4NwZAgJecP44T8B4LT3W9Yzg28Cz5Ps2Fh1wMdp1Zt14DTAwN1xEw5LHU5MDcMDmUfU9L3OPrWmPV9P0tUjAMMEDIlm5rCBPT5ClkLVWZTMAuS5M97C8BkBTwPtcCAEVEWZIGAC3jvtnnUN5vlseMIXhYEXHhDBMWSRewmJeUyVxdJ1R+Rx+TAFmZXs1VNX1fkpRWS11DSPJNFczuA7C51osM/1EvDS0Y2uDgupWisM0PCwytXWrt3F4QsMbcMcSz89+XBWF8/zYtSZrXAk/iAAArEk9ZF54wJ/5iIvm+gRfFFPFBMAU2sf5sIIoXEkrK3O3NdNs275dS9E6EHqtycg8Q/oWBJnbd6eUgpQGTgAciyKIQ+x9RCnx8s/JO3BkaaDvEEW+Gci5AKUmaLmuD8GF0nE1YeEYx4XRVrEWeyDUGXRPnHM+WDdrewIY8GIgRYpSRzhefhEkHDljhuEcSJDS5NUFN/BwLRAAphA1OuzUMIbkeAcCqv8lYAOujPIByd6rNysAwHA7Y5CImHpfYAQYtahXBm3ExCkzFf0ICTBgRRGyhQDquVAWYoAkl4NwSuwxRwVUABfkqBapQFfIAS/IszHUFjTTu9M+pM0lvNaWASpjgBMrouGGMALYziegPRjDZ6mwesbeBYUkEHyPmw9BHDMHL3yDfPhQRBGpWEXuURMR0pcIanxU0pU4DuJ/qPcce8UFNPAOwpQmD7BGK9h0/p3Ss74T6V0wIj8hnSJfrIlYw9lFwEAABEcA8Q1yuXAQABkTqPXIRbRUy4AzQ2maEpON0DLX/irfxzyTI6JWKYxgOAwrWI2IiNZz1oDJCcTtaxHj8lZlyHYAo7MEGWXWhVJAedVne0BNohBXMeYqUaWgjB58k6ITahsgRWzjwJREQ/CR51wizxGaXcZkzkrTIeLM1hCyWlLOpVSeivCiQAGs2VTAZRlJlcUQCyqCMQRlRJmXSBlVmQIpQFWIhVRykhfE+SAQFHATs5Q1WKKapy2udC/6T0ARfdeFZbbZDyHACC8RQqyXKIQlAMkugRg0r0wASYRetVHMQufQIJRv9XAAA1HAW4XY6KfkYuBOALEFaVkldxFVZQiLHhuOSuGZQ9VKu1OWnRwygRqNOUM6QybbhwFLWud0UxowUQjHhBUnURCNSeGRCiV4vFYsCHirAMRUBYsKedKAi9YgrIvmsvxQcKlT3VrEO8v5SLdrsMnRE2g56B0xVmM0LBkaKTxTYCGaq+3BJEFmNGrEr0UwbFgNw96RL9pCS+neTqDFxEfQO7giIABezgID6z/SIcGuD13nv5t8vG8sCZEzKBVREmLSW805mNUAaHkmYew5igjmA+bnQsouuIu62wdkclKjxEco5HphevM9s6Pa7xsFgXsyG4aodEOmg0Ros0sR2AASUFEECC/CA333CN631XrjyAGEicoyErixERAHCCnNsIdswl28i6KwChW4Hq304dI5CSHBAXQ864b9VJMQAc0hS1nCVWehzpYhPElQG5gIcaExUbhiR+ASQYD9Urkal+fmcCtsS0cEYESeOpkmXXdacagSJdyAJ6mFmrP6QEw4DLEzaFLBy4CCO5Rc22zgIl5LWN+CpdQC0YruVuDurhltGASp2CjnHLuLF/F+UBYngA2IS554RZOk11rPHXOPg822x43nlK+aWwFoJYHFuObS2gOAkSIDoHqtARJk2nUzbm+dAAtPduAAB1AIm9RyqwbgEJ9wyyhnbRKCMS+RoDVqE+9paO9NrbV2jLA6AXX1AennEUByhwFI0gfRJDMcAsWUR9u5e9F6rLzXVx2WAW5p8YE9j8n4Pt7o3UND6F7MeNTAR/opHTCjG0vqiWZGhA8DRigD4lxLd5EeNJj4rHLPeP8Y3eTv5YAeM0aXQTz8WOyc04WqOaXr6oeIr2gg6XFkgtOAjPtPDIBTVAUE/L7QmNCg9RotLlb7mkRNTKLlurOH0Se4OMid88vaOxEAAmEvvj1q+l6x9WdviAmTKDHkyZSkQtDKc7oLq30P8kdP9rELQcM4ZWA13Q/3oBu6xJHyO6t6N/nBSdaXnysamnr7ba9Zjmp3o7L+p9Yh5ds8YUXkBC5UcQO0pjssY6HA9rJNZt5f8pgu4CDBCgZrQnx4gOsBgmx41lHkpAbqcgQSF3OEuFoUFVzT6zAv0h2yI2hbVDGyNCYyjNpTaD+fCMR/QGIxh+AaLpAf3WmnxwFY2PEiXhCRCJyu2owKEr3HCAJAOfyTVfx4ym0YVmx4xfDNACEiT7RwU0DwRbAgLgEnCgP8FyHJDNFKDAG4FChn3oXOlQMVzhij3HHYkc1rxgDQ0YJ4wVibwC3Bx411wZ311h0EMA3Z3xyMSvh5z4D5wF2gGFzklcTBTF08W8V8VJzhzB0pyDg1yKSXTD1YDuwDFxhQ24P4K104Ph0h2EJh2pzhj7wOH8T0POjt2y2lygFQB73JyD2D24AGkXgLyaxoNylS1yCxiJD/wVmhUJRVg91qzAGhV0H92oNoOOGMJgKjnhkfDjwT2+WT1QwCxYLgGr1IgVgwIb2xjKERGTGsjEPWkYLiCLwyN11MI+XsWhQYFKGnwdVsyyKXxXw4NRTsF4N8kv3T1d0QK8zgHOC21XDLjhnMPOgEIcJsK2hENKHsKKkC2C39RgFyhAMxEjSBGACSzzyakRAwKXWDyAP60G0WjIAyMaNuyuORyH15FYHD3ACJwJTBBVn2gyNTxQyv2f32OALs292OK93OJWEuN22uNuJQHuOGyeJu3QN21xhE0YHokzRNBYhU24mdBdGM00QTFzBUz9QgkIjqxeDgHeAalzGk0FE8Un3RUAAwicocSAaIkE/eNAzBIhqDkpkiAEdOwcQTwbwJiOTcsLEvUDNcTPEz1JybGcIGTKogkgzLTNtXTfTFoDRB4bkiMP0ZguzfcFYYU0Us6c6O4wCB4hYOkhkibITEE4UuAIU2YNUi3FoDktoYAQ03khMfkoEfId0ooNUuAaXH4LkncZcQzNUIMurEM6YD0wUV4ndUKGwPSXgdAH2eicGMlQEtotlSgo0vom8c0lMkUyg0dPrJE204be014R02fZbCYgIIIi07mXmN0t3UM8Mvs5krs8LBdJdHxTM7rMaXMz8fM3mQs8pKYGU0TBiBU5iT1EA9OGYr1H1NTG4KCXMMocAnDU4aEZUlyHcFodEG0TkIwL0fgWUJUdIA8hEMobTHUr1CEcQIAA")[Link to a live lean version here]

To begin, let us define the function
$ "extend"
  (f : [n] arrow.r.hook [m]) (p : [m])
  (h : p in.not f^(-1)) : [n + 1] arrow.r.hook [m] =
  cases(
    p   & "if" 0,
    f n & "if" n + 1
  ) $

this is injective by definition using the arguemnt $h$.

#let coy = move(dx : 1pt, dy : 2pt, rotate([y], 180deg))

Now we will begin by showing the object isomorphism 
(note I use $coy (n)$ to represent the coyoneda functor at $n$).

#let psq = $accent(P, tilde)$

== $"iso" colon.eq forall P n, P(n)^n times P(n + 1) = psq (n) tilde.eq "obj"(P^N) = (coy (n) times N) -> P  $

Let us first define
$u : P(n)^n times P(n + 1) -> "Set"^(C)((coy (n) times N), P)$
as
$ u (chevron.l o_l, o_r chevron.r)_m (chevron.l p_l, p_r chevron.r) : P (m) eq.delta
  cases(
    P(p_l) (o_l v) & "if" exists v"," p_l v = p_r ,
    P("extend" p_l p_r "_") o_r & "otherwise"
  )
$

We need to show the naturality of $u(chevron.l o_l, o_r chevron.r)_m$,
for this consider a function $f : m -> m'$.

- *RTP*: $u(chevron.l o_l, o_r chevron.r)_(m) compose coy (f)_(n times f) = P(f) compose u(chevron.l o_l, o_r chevron.r)_m'$
- *Function extentionality* with $(chevron.l p_l, p_r chevron.r)$
- *Case* with $exists v, f (p_l v) = f p_r,$
  - *RTP*: $P (f compose p_l) (o_r v) = P (f) (P (p_l) (o_r v))$
  - Which is true by functorality in $P$
- *Case* with $not exists v, f (p_l v) = f p_r,$
  - *RTP*: $P ("extend" (f compose p_l) (f p_r) "_") o_r = (P (f) compose P ("extend" p_l p_r "_")) o_r = P(f compose "extend" p_l p_r "_") o_r$
  - *By congruence*
  - *RTP*: $("extend" (f compose p_l) (f p_r) "_") = f compose "extend" p_l p_r "_"$
  - *Function extentionality* with $i$
  - *Case* $i = 0$
    - *RTP*: $f p_r = f p_r$
    - True by refl
  - *Case* $i = n+1$
    - *RTP*: $f (p_l n) = f (p_l n)$
    - True by refl

We then define
$v : "Set"^(C)((coy (n) times N), P) -> P(n)^n times P(n + 1)$
as
$ v(t) : P (n)^n × P (n + 1) eq.delta chevron.l lambda i. t_n chevron.l id, i chevron.r , t_(n+1) chevron.l "succ", 0 chevron.r chevron.r $

Now we have to prove that $u compose v = id$

- *RTP*: $(u (v t))_m (chevron.l i_l, i_r chevron.r) 
          = cases(
              P(i_l) (t_n (chevron.l id, v chevron.r)) && "if" exists v"," i_l v = i_r,
              P("extend" i_l i_r "_") (t_(n+1) (chevron.l "succ", 0 chevron.r)) && "otherwise" )
          = t_m (chevron.l i_l ,i_r chevron.r)$
- *Case* $exists v, i_l v = i_r$
  - $ 
      (P(i_l) compose t_n) (chevron.l id, v chevron.r) &= t_m (chevron.l i_l compose id, i_l v chevron.r) && "by naturality of" t \
      &= t_m (chevron.l i_l , i_r chevron.r) && "by defn of "v \
      &= t_m (chevron.l i_l , i_r chevron.r)
    $
- *Case* otherwise
  - $
    (P("extend" i_l i_r "_") compose t_(n+1)) ("succ", 0)
    &= t_m ("extend" i_l i_r "_" compose "succ", "extend" i_l i_r "_" 0) && "by naturality of "t\
    &= t_m ("extend" i_l i_r "_" compose "succ", i_r) && "by defn of extend" \
    &= t_m (i_l, i_r) && "by defn of extend" \
  $

Finally $v compose u = id$,

- *RTP*: $v (u (chevron.l i_l, i_r chevron.r)) = chevron.l i_l, i_r chevron.r$
- using *product extentionality*
- *Case*: fst *RTP*: $(v (u (chevron.l i_l, i_r chevron.r))).1 = i_l$
  - apply *Function extentionality* with $j$
  - *RTP*: $cases(P (id) (i_l j) & "if " exists v"," id v = i, P ("extend" (id) i "_") i_r) = i_l j$
  - There exists a $id v = i$, exacly $i$
  - *RTP*: $P (id) (i_l j) = i_l j$
  - $P (id) (i_l j) = id (i_l j) = i_l j$
- *Case*: snd *RTP*: $(v (u (chevron.l i_l, i_r chevron.r))).2 = i_r$
  - *RTP*: $cases(P ("succ") (i_l v) & "if" exists v "," "succ" v = 0, P("extend" "succ" 0 "_") i_r & "otherwise") = i_r$
  - There doesn't exist some $v$ such that $v+1 = 0$
  - *RTP*: $P("extend" "succ" 0 "_") i_r = i_r = id i_r = P(id) i_r$
  - By *congruence* we are
  - *RTP*: $"extend" "succ" 0 "_" = id$
  - apply *Function extentionality* with $i$
  - *Case* $i = 0$
    - $0 = id 0$
  - *Case* $i = n + 1$
    - $n + 1 = id (n + 1)$

We are now done and have the isomorphism $"iso"$.

== Defining the map $psq(f) : psq(n) -> psq(m)$

We define the map as $P(f) eq.delta "iso"_"symm" compose P^N (f) compose "iso"$,
its functorality is easy to prove

$ psq(id) &= "iso"_"symm" compose P^N (id) compose "iso" \
&= "iso"_"symm" compose id compose "iso" && "By functorality of "P^N \
&= "iso"_"symm" compose "iso" \
&= id $

$ psq(f compose g) &= "iso"_"symm" compose P^N (f compose g) compose "iso" \
&= "iso"_"symm" compose P^N (f) compose P^N (g) compose "iso" && "By functorality of "P^N \
&= "iso"_"symm" compose P^N (f) compose id compose P^N (g) compose "iso" \
&= "iso"_"symm" compose P^N (f) compose "iso" compose "iso"_"symm" compose P^N (g) compose "iso" \
&= psq (f) compose psq (g) $

== $psq tilde.eq P^N$

To construct the isomorphism,
we simply have to prove that $"iso"$ is natural.
By the way we picked the morphism map we get both of these for free:
$"iso" compose psq (f) = "iso" compose "iso"_"symm" compose P^N (f) compose "iso" = P^N (f) compose "iso"$,
and the other direction follows by analogy.

== $"app" : psq times N -> P$

We define app quite simply as
$"app" eq.delta "app"_(P^N) compose ("iso" times id)$.
By construction, this satisfies the required universal property.

#pagebreak()

= Question 5

I have identified that the structure $S(I)$ is the Schanuel topos (nominal sets).
Therefore the functor we are looking for is the sheafification functor.
I have desperately tried to construct this.
I see the object of the functor will be some quotient over what looks like products of a hom and an object of the presheaf,
the exact object and relation are lost to me.
I sadly think my knowledge of the course is not sufficent for this.

#pagebreak()

= Formally verified solutions <lean>

#let N = 4

#for i in range(N) {
  let i = 1+i
  heading(level : 2, "Q" + str(i))
  raw(read("./Cat/Exam/Q" + str(i) + ".lean"), block : true, lang : "lean")
  if i != N { pagebreak() }
}

