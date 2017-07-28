\documentclass[12pt, letterpaper]{article}

\usepackage[greek,english]{babel}
\usepackage[T1]{fontenc}

\usepackage{float}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{bbold}
\usepackage{stmaryrd}
\usepackage{multicol}

\usepackage{hyperref}
\usepackage{agda}

\setmainfont{TeX Gyre Termes}
%\setmathfont{XITS Math}
\setsansfont[Scale=MatchLowercase]{DejaVuSansMono.ttf}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}{Lemma}[section]
\newtheorem{axiom}{Axiom}[section]
\newtheorem{conjecture}{Conjecture}[section]

\newcommand{\inl}{\textsf{inl}}
\newcommand{\inr}{\textsf{inr}}
\newcommand{\abst}[2]{\lambda #1\to#2}
\newcommand{\refl}{\textsf{refl}}
\newcommand{\funext}{\textsf{funext}}

\title{Completeness of $\Pi$}
\author{Siva Somayyajula}
\date{July 2017}

\begin{document}
\maketitle

\begin{abstract}
$\Pi$ is a reversible programming language by Sabry et al. inspired by type-theoretic isomorphisms. We give a model for $\Pi$: a univalent universe of finite types in homotopy type theory. Using properties of \emph{univalent fibrations}, the underlying concept of this model, we give formal proofs in Agda that programs in $\Pi$ are complete with respect to this model. Additionally, we discuss this model and extensions to $\Pi$ through the lens of synthetic homotopy theory.
\end{abstract}

\tableofcontents

\section{Introduction}

\subsection{Reversibility}

Reversibility is the notion that computations and their effects may be reversed. This is prevalent in computing applications, giving rise to ad hoc implementations in both hardware and software alike. In particular, transactional databases operate on the basic concept that operations on data may be committed to memory or rolled back, and version control systems like \texttt{darcs} are based on \emph{patch theory}, an algebra for file changes. At the software level, this has motivated the development of general-purpose reversible programming languages---Janus, developed in 1982, is such a language with a formally verified interpreter.

While Janus is designed for imperative programming, there has not yet been such an effort for functional programming, whose emphasis on avoiding mutability, amongst other things, is amenable to reversibility. To elaborate, a natural type-theoretic notion of reversibility is given by type isomorphisms i.e. lossless transformations over structured data. Thus, a calculus for such isomorphisms would give rise to a reversible functional programming language. The $\Pi$ programming language introduced by Sabry et al.is precisely that. However, to understand $\Pi$ and its model, we give a brief introduction to type theory and its homotopy-theoretic interpretation.

\subsection{Type Theory}

A type theory is a formal system for \emph{types}, \emph{terms}, and their computational interactions. A helpful analogy to understand type theory at first is to conceptualize types as sets and terms as their elements. Like set theory, type theories have rules governing \emph{type formation} as there are axioms about set construction e.g. the axiom of pairing, but there are important distinctions. Whereas set theory makes set membership a proposition provable within the system, terms do not exist without an a priori notion of what type they belong to---one writes $a : A$ (pronounced ``$a$ inhabits $A$'') to introduce a term $a$ of type $A$. As a result, terms are also called \emph{inhabitants}, and we will use those terms (pun intended) interchangeably throughout the rest of the paper.

Perhaps the distinguishing feature of type theories are their explicit treatment of computation: computation rules dictate how terms reduce to values. To programming language theorists, type theories formally describe programming languages and computation rules are precisely the structured operational semantics. On the other hand, set theories have no such equivalent concept.

This emphasis on computation has several applications to computer science. First, the type systems of such programming languages as Haskell are based on certain type theories (specifically, System F). Aside from their utility in programming language design, sufficiently sophisticated type theories are suitable as alternative foundations of mathematics to set theory. In fact, Martin-L\"of type theory (MLTT) is the basis of many programs aiming to formalize constructive mathematics. To understand how this is possible, recall that set theories consist of rules governing the behavior of sets as well as an underlying logic to express propositions and their truth. Thus, it remains to show that type theories, under the availiblity of certain type formers, are languages that can express the construction of arbitrary mathematical objects as well as encode propositions as types and act as deductive systems in their own right.

Thus, we will first give a brief introduction to MLTT in Agda, a programming language and proof assistant based on MLTT.

\subsection{Martin-L\"of Type Theory}
Continuing the analogy that types are sets, the following table describes the set-theoretic analogue of each type former in MLTT. The syntax of the terms inhabiting these types are in almost one-to-one correspondence with classical mathematics, with caveats explained below.

\begin{center}
\begin{tabular}{ c|c } 
 \hline
 type & set \\
 \hline
 $U$ or \AgdaDatatype{Type} & universal set\\
 $\mathbb{0}$ & $\emptyset$\\
 $\mathbb{1}$ & singleton\\
 $\mathbb{N}$ & Peano numbers\\
 $A + B$ & coproduct $A\sqcup B$\\
 $A\times B$ & $A\times B$\\
 $A\to B$ & function space $B^A$
\end{tabular}
\end{center}

The function type is perhaps the most novel type to mathematicians who are used to set theory. First, functions are no longer specialized sets amenable to implicit descriptions, so we require an explicit syntax to construct them. Inspired by Alonzo Church's lambda calculus, functions of type $A\to B$ are written $\abst{x}{e}$ (called a \emph{lambda abstraction}) where $x$ is the argument of type $A$ and $e$ is an expression of type $B$ that may freely use $x$. In Agda, one may either use lambda abstractions or traditional mathematical notation to write functions---we will use both throughout this paper. Then, to apply a function $f$ to argument $x$, one can write either $f~x$ or $f(x)$---we will use the former in writing Agda and the latter elsewhere. As an example, consider the following definition of $\AgdaFunction{add}$ for the natural numbers. First, the type of the term is declared and then the definition is given.

\begin{AgdaAlign}
\AgdaHide{
\begin{code}
module Pi where

open import Type

module Ex1 {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  open import UnivalentTypeTheory hiding (add; 𝟚)
\end{code}}
\begin{code}
  add : ℕ → ℕ → ℕ
  add 0        n = n
  add (succ m) n = succ (add m n)
\end{code}

This definition makes use of \emph{currying}---as opposed to writing this multiargument function as being of type $\mathbb{N}\times\mathbb{N}\to\mathbb{N}$, we have written a function that consumes an argument of type $\mathbb{N}$--the first argument--and then returns a function of type $\mathbb{N}\to\mathbb{N}$ that consumes the second argument and produces the sum. While the syntactic shortcuts of Agda abstract this distinction away; one could have written $\abst{m}{\abst{n}{\ldots}}$. Thus, in classical mathematics, $add$ would be applied as $add(1)(2)$. This technique is common in type theory and will be preferred to traditional notation in this paper. Now, to demonstrate the promises of computational benefits by MLTT, we can request Agda to evaluate the following expression:

$$\AgdaFunction{add}~1~2\to 3$$

For all types $A$ and $B$, we can also write a function that swaps the components of a tuple in $A\times B$ and run it on a pair of natural numbers.

\begin{code}
  swap : A × B → B × A
  swap (a , b) = (b , a)
\end{code}

$$\AgdaFunction{swap}~(1 , 2)\to(2 , 1)$$

Furthermore, we can define types of our own, like $\mathbb{2}$: the Boolean type consisting of two \emph{canonical inhabitants} representing truth values.

\begin{code}
  𝟚 : Type₀
  𝟚 = 𝟙 + 𝟙

  pattern true  = i₁ 0₁
  pattern false = i₂ 0₁
\end{code}

We use the term \emph{canonical} to distinguish \emph{values} inhabiting types, as opposed to the infinite possible expressions that evaluate to said values. Here, $\AgdaFunction{i_1}$ and $\AgdaFunction{i_2}$ are the canonical injections of $A$ and $B$ into $A + B$, respectively. Furthermore, $0_1$ is the canonical inhabitant of $\mathbb{1}$. Agda's pattern syntax allows us to associate the names \AgdaInductiveConstructor{true} and \AgdaInductiveConstructor{false} with the given values.

This is also our first exposure to MLTT's universe. To avoid Russell's paradox, the universe of types does not contain itself. Instead, Agda has a hierarchy of universes where $U_0$ is the universe of small types inhabited by $\mathbb{0}$, $\mathbb{1}$, $\mathbb{ℕ}$, etc. Further universes are given by $U_i:U_{i+1}$ and the various type formers like the coproduct inhabit different universes based on its component types. For brevity, we will switch between employing \emph{typical ambiguity}, eliding which universe we are working in by simply writing $U$, and specifying the level explicitly in code. Now, we may write a function $P:\mathbb{2}\to U$.

\begin{code}
  P : 𝟚 → Type₀
  P true  = 𝟙
  P false = 𝟘
\end{code}

Note that functions like this whose codomains are universes are called \emph{type families}, as they return types instead of ordinary terms.

MLTT then introduces \emph{dependent types}, which generalize the function and Cartesian product types.

\begin{definition}[Dependent types]
Let $A$ be a type and $P:A\to U$ be a type family. The \emph{dependent function} type $\prod_{a:A}P(a)$ is inhabited by functions $f$ where if $a : A$, then $f(a):P(a)$ i.e. functions whose codomain type varies with their input.

Similarly, the \emph{dependent pair} type $\sum_{a : A}P(a)$ is inhabited by $(a, b)$ where $a : A$ and $b : P(a)$ i.e. pairs where the type of the second component varies with the first component.
\end{definition}

The utility of these two type formers is elucidated in the following explanation: while we now have a calculus to express arbitrary mathematical objects, we still lack a deductive system to perform mathematical reasoning. In order to develop this, we must first introduce the \emph{Brouwer-Heyting-Kolmogorov (BHK) interpretation}, which not only captures the intuition for proofs in informal mathematics but also expresses them as computable objects.

\begin{definition}[BHK interpretation]
We define a proof by induction on the structure of a logical formula.
\begin{itemize}
\item There is no proof of $\bot$
\end{itemize}

Now, let $a$ be a proof of $A$ and $b$ be a proof of $B$. A proof of\ldots
\begin{itemize}
\item \ldots$A\land B$ is $(a, b)$ i.e. a proof of $A$ \emph{and} a proof of $B$
\item \ldots$A\lor B$ is either $(0, a)$ or $(1, b)$ i.e. a proof of $A$ \emph{or} a proof of $B$
\item \ldots$A\implies B$ is a computable function that converts a proof of $A$ to a proof of $B$
\item \ldots$\lnot A$ is a proof of $A\implies\bot$
\end{itemize}

Then, fix a domain of discourse $D$. A proof of\ldots
\begin{itemize}
\item \ldots$\forall_{x\in D}P(x)$ is a computable function that converts $a\in D$ to a proof of $P(a)$
\item \ldots$\exists_{x\in D}P(x)$ is a pair $(a, b)$ where $a\in D$ and $b$ is a proof of $P(a)$ 
\end{itemize}
\end{definition}

The proofs described by this interpretation are in exact one-to-one correspondence with the terms inhabiting the various type formers we have just introduced, as shown below.

%\begin{figure}[H]
\begin{center}
\begin{tabular}{ c|c } 
 \hline
 proposition & type \\
 \hline
 $\bot$ & $\mathbb{0}$\\
 $\top$ & $\mathbb{1}$\\
 $A\lor B$ & $A + B$\\
 $A\land B$ & $A\times B$\\
 $A\implies B$ & $A\to B$\\
 $\lnot A$ & $A\to\mathbb{0}$\\
 type family & predicate\\
 $\forall_{a\in A}P(a)$ & $\prod_{a:A}P(a)$\\
 $\exists_{a\in A}P(a)$ & $\sum_{a:A}P(a)$
\end{tabular}
\end{center}
%\end{figure}

We can make concrete the correspondence between propositions and types (and consequently proofs and terms) below.

\begin{definition}[Propositions-as-types]
Let $A$ be a type representing a proposition $P$. If $a : A$, then $a$ is a proof of $P$ in the sense of the BHK interpretation.
\end{definition}

With this principle in mind, we can prove some basic propositions in constructive logic, like DeMorgan's law: $\lnot A\land\lnot B\iff\lnot(A\lor B)$.

\begin{code}
  DeMorgans₁ : ¬ A × ¬ B → ¬ (A + B)
  DeMorgans₁ (¬a ,   _) (i₁ a) = ¬a a
  DeMorgans₁ (_  ,  ¬b) (i₂ b) = ¬b b

  DeMorgans₂ : ¬ (A + B) → ¬ A × ¬ B
  DeMorgans₂ ¬a+b = ((λ a → ¬a+b (i₁ a)) , (λ b → ¬a+b (i₂ b)))
\end{code}

Computationally, DeMorgan's law is simply the universal property of the coproduct. Given morphisms $A\to\mathbb{0}$ and $B\to\mathbb{0}$, one can construct a morphism $A + B\to\mathbb{0}$ and vice versa. As a result, the propositions-as-types principle reduces theorem proving to a purely computational endeavor. Now, we can examine the dependent function and pair types. Let us first define the $\leq$ relation on the natural numbers---in MLTT, it is a type family indexed by two natural numbers.

\AgdaHide{
\begin{code}
module Ex2 where
  open import UnivalentTypeTheory
\end{code}}
\begin{code}
  _≤_ : ℕ → ℕ → Type₀
  0 ≤ n               = 𝟙
  (succ m) ≤ (succ n) = m ≤ n
  m ≤ n               = 𝟘
\end{code}

This definition is quite straightforward: for any number $n$, $0\le n$, and $S(m)\leq S(n)$ if and only if $m\le n$. Otherwise, the relation does not hold i.e. is defined as absurdity. This allows us to construct computable evidence that a certain number is less than or equal to another one. We can now prove a basic result like $∀_{n ∈ ℕ}\lnot(S(n)\leq n)$ by writing a dependent function. Note that in Agda, the dependent function type $\prod_{a:A}P(a)$ is written $(a:A)\to P(a)$.

\begin{code}
  -- The codomain type varies on n
  succ-n≰n : (n : ℕ) → ¬ (succ n ≤ n)
  -- By induction on n
  succ-n≰n 0        = id
  succ-n≰n (succ n) = succ-n≰n n
\end{code}

For the base case, the goal $\lnot(1\leq 0)$ evaluates to $\mathbb{0}\to\mathbb{0}$. Thus, a term of this type is the identity function. For the inductive step, realize that the goal $\lnot(S(S(n))\leq S(n))$ evaluates to $\lnot(S(n)\leq n)$. By induction, $\AgdaFunction{succ-n\leq n~n}:\lnot(S(n)\leq n)$, so the proof is complete.

%The main two points here are that (1) dependent functions compute the evidence of universally quantified formulas and (2) the principle of mathematical induction is computationally dual to recursion. There are other deep relationships between computation and logic due to propositions-as-types, but those are beyond the scope of this report.

As stated before, existential quantification is encoded as the dependent pair type---in Agda, $\sum_{a:A}P(a)$ is written \AgdaDatatype{Σ~A~P}. Now, we can prove the analogous proposition that for any set $A$ and predicate $P$ on $A$, $\lnot\exists_{a\in A}P(a)\implies\forall_{a\in A}\lnot P(a)$.

\AgdaHide{
\begin{code}
module Ex3 {ℓ} {ℓ'} {A : Type ℓ} {P : A → Type ℓ'} where
  open import UnivalentTypeTheory
\end{code}}
\begin{code}
  ¬Σ-is-Π¬ : ¬ (Σ A P) → (a : A) → ¬ (P a)
  ¬Σ-is-Π¬ ¬Σ a Pa = ¬Σ (a , Pa)
\end{code}

As a result, we could have proven the penultimate result using existential quantification.

\AgdaHide{
\begin{code}
module Ex4 where
  open import UnivalentTypeTheory
  open Ex2
  open Ex3
\end{code}}
\begin{code}
  succ-n≰n' : (n : ℕ) → ¬ (succ n ≤ n)
  succ-n≰n' = ¬Σ-is-Π¬ lemma where
    -- By induction on n
    lemma : ¬ (Σ ℕ (λ n → succ n ≤ n))
    lemma (0      , 1≰0)      = 1≰0
    lemma (succ n , succ-n≰n) = lemma (n , succ-n≰n)
\end{code}

The identification of types and propositions mean that proofs are themselves mathematical objects that may be reasoned about---that is, we are doing \emph{proof-relevant mathematics}. Furthermore, the computational content of MLTT is directly accessible. Although these examples are quite tame, more complex proofs are of great utility in software engineering. For example, Euclid's proof of the existence of a greatest common factor formalized in a language like Agda is an executable algorithm which finds precisely that. The implications of proof relevance, amongst other things, have motivated the development of \emph{homotopy type theory}, the type theory underlying the results of this paper.

\subsection{Homotopy Type Theory}

In the previous section, we gave an informal exposition of MLTT by appealing to set theory---in other words, we interpeted the various type formers as set constructors, terms as elements, and discussed their computational and logical interactions. However, we are missing a type that expresses \emph{propositional equality} i.e. propositions that two objects $a$ and $b$ are equal.

\begin{definition}[Identity type]
For all types $A$ and $a , b : A$, the \emph{identity type} $a = b$ is inhabited by proofs that $a$ and $b$ are equal, called \emph{identifications}.

By definition, the canonical method of introducing an inhabitant of this type is by reflexivity: $\refl=\prod_{a:A}a=a$.
\end{definition}

Structural induction upon terms of this type is not as straightforward as with the other type formers. One would expect to be able to simply reduce every encounter of the identity type to reflexivity during theorem proving, but that defies the homotopy-theoretic interpretation of type theory. When types are interpreted as spaces and terms as points, we get the following correspondence.

\begin{center}
\begin{tabular}{ c|c } 
 \hline
 type theory & homotopy theory\\
 \hline
 type & space\\
 term & point\\
 type family & fibration\\
 $a=b$ & path space
\end{tabular}
\end{center}

The last point is crucial---the identity type on points $a$ and $b$ is interpreted as the space of paths from $a$ to $b$. As a result, being able to reduce any term inhabiting the identity type to reflexivity is tantamount to contracting any path to a constant loop, which is nonsensical in homotopy theory! In fact, only when at least one endpoint---either $a$ or $b$---is free to vary, can one contract a path to a constant loop by moving the free point to the other. This intuition allows us to first define the $PathFrom$ type family, which maps a fixed point $x$ to the space of paths emanating from it i.e. an entire subspace of free points.

\AgdaHide{
\begin{code}
module Ex5 {ℓ} {A : Type ℓ} where
  open import UnivalentTypeTheory
  
  PathFrom : A → Type ℓ
  PathFrom x = Σ A (λ y → x == y)

  J : ∀ {ℓ'} {x : A} (P : PathFrom x → Type ℓ') → P (x , refl x) → (p : PathFrom x) → P p
  J _ b (x , refl .x) = b
\end{code}}

\begin{definition}[PathFrom]
$$PathFrom(x)\triangleq\sum_{y:A}x=y$$
\end{definition}

The following principle then allows us to reduce certain paths to constant loops under the exact conditions described.

\begin{definition}[Paulin-Mohring's J]
Given a type family $P:PathFrom(x)\to U$, $J:P(x, \refl{x})\to\prod_{p:PathFrom(x)}P(p)$ with the following computation rule:
$$J(r, (x, \refl{x}))\mapsto r$$
\end{definition}

Thus, it is impossible to prove that \emph{all} inhabitants of the identity type are identical to reflexivity (see Hofmann and Streicher's groupoid model of type theory). Likewise, not every path is contractible to a constant loop. In fact, one can only prove that inhabitants of $PathFrom(x)$ are propositionally equal to $(x, \refl(x))$ since the second endpoint is left free.

\AgdaHide{
\begin{code}
module Ex6 {ℓ} {A : Type ℓ} {x : A} where
  open import UnivalentTypeTheory
  open Ex5
\end{code}}
\begin{code}
  PathFrom-unique : (yp : PathFrom x) → yp == (x , refl x)
  PathFrom-unique = J (λ yp → yp == (x , refl x)) (refl (x , refl x))
\end{code}

As a result, this allows us to add so-called nontrivial inhabitants to the identity type via separate inference rules without rendering the system inconsistent. Motivated by the simplicial set model of type theory by Awodey et al., HoTT adds such inhabitants expressing the extensional equality of various objects. For example, given functions $f,g:A\to B$, if one has evidence $\alpha:\prod_{x:A}f(x)=g(x)$, the axiom of function extensionality gives $\funext(\alpha):f=g$. However, the crux of HoTT lies in Voevodsky's univalence axiom, which is an extensionality axiom for \emph{types}. Before we introduce it, we must first define what it means for two types to be extensionally equal.

\begin{definition}[Quasi-inverse]
A \emph{quasi-inverse} of a function $f:A\to B$ is the following dependent triple:
\begin{itemize}
\item $g:B\to A$
\item $\alpha:\prod_{x:A}g(f(x))=x$
\item $\beta:\prod_{x:B}f(g(x))=x$
\end{itemize}
\end{definition}

For the purposes of this paper, we will refer to functions that have quasi-inverses as equivalences, although there are other equivalent notions in type theory. In Agda, we must explicitly specify which type of equivalence we are providing i.e. \AgdaFunction{qinv-is-equiv} for quasi-inverses. We can now give our notion of extensionality for types.

\begin{definition}[Type equivalence]
Given types $X$ and $Y$, $X\simeq Y$ if there exists a function $f:X\to Y$ that is an equivalence.
\end{definition}

Perhaps the most trivial equivalence is given below.

\begin{theorem}[Identity equivalence]
For any type $A$, $A\simeq A$ by the identity function---the dependent pair of $id$ and evidence that it has a quasi-inverse is called $\AgdaFunction{ide}~A$ in Agda.
\end{theorem}

An immediate result is that an equality between types can be converted to an equivalence.

\begin{theorem}[\AgdaFunction{idtoeqv}]
For all types $A$ and $B$, $A=B\to A\simeq B$.
\end{theorem}
\begin{proof}
Using J reduces the proof goal to giving a term of type $A\simeq A$ i.e. the identity equivalence.
\AgdaHide{
\begin{code}
module Ex7 {ℓ} {A B : Type ℓ} where
  open import UnivalentTypeTheory
  open Ex5
\end{code}}
\begin{code}
  idtoeqv : A == B → A ≃ B
  idtoeqv p = J (λ{(B , _) → A ≃ B}) (ide A) (B , p)
\end{code}
\end{proof}

\begin{axiom}[Univalence]
\textsf{idtoeqv} is an equivalence.
\end{axiom}

By declaring that \textsf{idtoeqv} has a quasi-inverse, this axiom gives us the following data:

\begin{itemize}
\item $\textsf{ua}:A\simeq B\to A = B$, a function that converts equivalences to paths
\item $\textsf{ua}\-\beta:\prod_{f:A\simeq B}\textsf{idtoeqv}(\textsf{ua}(f))=f$
\item $\textsf{ua}\-\eta:\prod_{f:A\simeq B}\textsf{ua}(\textsf{idtoeqv}(p))=p$
\end{itemize}

The last two data are called \emph{propositional computation rules}, as they dictate how \textsf{ua} reduces propositionally, outside of the computation rules built into type theory. However, this raises the question: how do terms evaluate to a value in the presence of univalence? This is actually still an open question---for now, homotopy type theory lacks \emph{canonicity}, the guarantee that every term has a canonical form.

Univalence is justified when we broaden our interpretation of types to not just spaces but to \emph{homotopy types}---spaces regarded up to homotopy equivalence. In that sense, $ua$ is simply the trivial assertion that spaces that are homotopy equivalent are equal (up to homotopy equivalence).

Before moving onto $\Pi$ and its model, we must establish one last concept and rethink our previous conception of propositions-as-types. Recall that we are doing proof-relevant mathematics. However, classical mathematics is decidedly proof-irrelevant since propositions are simply assigned a truth value without additional information. In terms of type theory, this would mean the terms of every type would be indistinguishable up to propositional equality. As a result, the only information we would have about a tautology encoded as a type is that it is inhabited by \emph{some} value, and an absurdity would simply be uninhabited. We formalize this intuition below.

\begin{definition}[Mere proposition]
A type is a \emph{mere proposition} if all of its inhabitants are propositionally equal. That is, the following type is inhabited:

$$isProp(A) = \prod_{x,y:A} x == y$$
\end{definition}

This allows us to formalize analogies between classical mathematics (we avoid the phrase ``classical logic'', which is related to mere propositions but not expounded here) and type theory.

\begin{theorem}[Logical equivalence]
For all mere propositions $A$ and $B$, if $A\to B$ and $B\to A$, then $A\simeq B$. That is, to show that two mere propositions are equivalent, it is sufficient to show that they are logically equivalent.
\end{theorem}
\begin{proof}
To show $f:A\to B$ and $g:B\to A$ are inverses, we identify $g(f(x))$, $x$, $f(g(y))$ and $y$ for $x:A$, and $y:B$, respectively, by the fact that $A$ and $B$ are mere propositions.
\AgdaHide{
\begin{code}
module Biconditional {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  open import UnivalentTypeTheory
  open import OneTypes
\end{code}}
\begin{code}
  logical-equiv :
    is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
  logical-equiv pA pB f g =
    f , qinv-is-equiv (g , (λ x → pA (g (f x)) x) , (λ y → pB (f (g y)) y))
\end{code}
\end{proof}

For types that are not mere propositions, we may construct an analogue that is.

\begin{definition}[Propositional truncation]
For a type $A$, its propositional truncation $\parallel A\parallel$ is described by the following
\begin{itemize}
\item If $a : A$, then $\mid a\mid:\parallel A\parallel$
\item $\textsf{identify}:\Pi_{x,y:\parallel A\parallel} x == y$
\end{itemize}

By $\textsf{identify}$, the propositional truncation of any type is a proposition, hence the name.
\end{definition}

Structural induction upon inhabitants of a propositional truncation is subtle---a function can only recover the original term underneath the truncation bars if its codomain itself is a mere proposition. We will see this principle show up as \AgdaFunction{recTrunc} later on.

In short, mere propositions allow us to encode proof-irrelevance into type theory. This is key in defining the \emph{univalent universe of finite types}, the model of $\Pi$, which we will do in the next section.

\section{Univalent Universe of Finite Types}

\subsection{Univalent Fibrations}

An elementary result in homotopy theory is that a path between points $x$ and $y$ in the base space of a fibration induces an equivalence between the fibers over $x$ and $y$. By univalence, this equivalence is a path as well. We formalize this result below.

\begin{theorem}[\AgdaFunction{transporteqv}]
For any type $A$ and $x, y : A$, $\prod_{P:A\to U}x=y\to P(x)≃P(y)$.
\end{theorem}
\begin{proof}
By J, we may reduce the proof goal to giving a term of type $P(x)\simeq P(x)$ i.e. the identity equivalence.
\AgdaHide{
\begin{code}
module Ex8 {ℓ} {ℓ'} {A : Type ℓ'} {x y : A} where
  open import UnivalentTypeTheory
  open Ex5
\end{code}}
\begin{code}
  transporteqv : (P : A → Type ℓ) → x == y → P x ≃ P y
  transporteqv P p = J (λ{(y , _) → P x ≃ P y}) (ide (P x)) (y , p)
\end{code}
\end{proof}

However, converse is not always true---type families that satisfy this property are called {univalent fibrations}.

\begin{definition}[Univalent Fibration]
For all types $A$, a type family $P : A → U$ is a \emph{univalent fibration} if $\textsf{transporteqv}(P)$ is an equivalence.
\end{definition}

That is, univalent fibrations come with a quasi-inverse of \textsf{transporteqv} that converts fiberwise paths to paths in the base space. Even though it is rarely the case that any given type family is a univalent fibration, the following theorem characterizes a class of families that are.

\begin{theorem}[Christensen, Rose]
\label{predExtIsUniv}
Let $P:U\to U$ be a type family. If for all $X : U$, $P(X)$ is a mere proposition, then the first projection $p_1:\sum_{X:U}P(X)\to U$ is a univalent fibration.
\end{theorem}

\subsection{The \AgdaFunction{is-finite} Family}
\AgdaHide{
\begin{code}
module Ex9 where
  open import UnivalentTypeTheory
  open import PropositionalTruncation
\end{code}}
We will now examine the \AgdaFunction{is-finite} type family which forms the basis of the model for $\Pi$. First, we require a canonical notion of a finite type.

\begin{definition}[\AgdaFunction{El}]
The \AgdaFunction{El} family sends a natural number $n$ to a finite type with $n$ canonical inhabitants.
\begin{code}
  El : ℕ → Type₀
  El 0        = 𝟘
  El (succ n) = 𝟙 + El n
\end{code}
\end{definition}

To see that this definition is sufficient, we can enumerate all $n$ canonical inhabitants of $\AgdaDatatype{El}~n$.

\begin{center}
\begin{tabular}{ c|l }
 1 & $i_1(0_1)$ \\
 2 & $i_2(i_1(0_1))$\\
 3 & $i_2(i_2(i_1(0_1)))$\\
 \vdots & \vdots\\
 n & $\underbrace{i_2(i_2(\ldots}_{n}(i_1(0_1))\ldots))$
\end{tabular}
\end{center}

Notice that we never reach $i_2(i_2(\ldots(i_2(...))\ldots))$ because that would require giving an inhabitant of $\mathbb{0}$, which is impossible. Thus, we are guaranteed $n$ canonical inhabitants.

%This pattern allows us to give a Peano numbers-like representation of these values via the following additions to the syntax.

Now, we are ready to define the $\AgdaFunction{is-finite}$ family.

\begin{code}
  is-finite : Type₀ → Type₁
  is-finite A = Σ ℕ (λ n → ∥ A == El n ∥)
\end{code}

Viewed as a predicate, this says ``a type is finite if it is equivalent to a finite type''. Computationally, we require a proof-irrelevant identification of $A$ and $\AgdaDatatype{El}~n$ for some $n$. Then, we define the univalent universe of finite types to be the subuniverse of types satisfying this predicate.

\begin{code}
  M : Type₁
  M = Σ Type₀ is-finite
\end{code}

Terms of this type are triples consisting of (1) a type $A$, (2) the ``size'' of $A$, and (3) a path witnessing the given size is correct by identifying $A$ with a canonical finite type of the same size. The following diagram gives some inhabitants of $M$.

\begin{figure}[H]

\end{figure}

The reason we truncate the above instance of the identity type is to yield the following result.

\begin{theorem}[Rose, 2017]
\label{finiteTypeIsUniv}
The first projection $p_1$ of triples in $M$ is a univalent fibration.
\end{theorem}
\begin{proof}
For any $A$, $isFinite(A)$ is a mere proposition due to the truncation of its second componet, amongst other things. Thus, from theorem \ref{predExtIsUniv}, $p_1$ is a univalent fibration.
\end{proof}

This is the workhorse of our completeness result---intuitively, to induce a path between two triples, one simply needs to give an equivalence between their first components, which minimizes our proof obligations.

\section{Pi}

Now that we are acquainted with HoTT and finite types, we can examine the $\Pi$ programming language by Sabry et al. $\Pi$ starts with the notion that type equivalences are a natural expression of reversibility---one can write and execute a program and invert its effects via its quasi-inverse. $\Pi$ then restricts its type calculus to the semiring $(\{\mathbb{0},\mathbb{1}\},+,\times)$ up-to type equivalence. As a result, a complete characterization of equivalences over these types is precisely the semiring axioms, show below. Note that $\Pi$ uses $\leftrightarrow$ for $\simeq$.

\AgdaHide{
\begin{code}
open import UnivalentTypeTheory hiding (𝟚)
open import PropositionalTruncation
open import EmbeddingsInUniverse
open UnivalentUniverseOfFiniteTypes

M : Type₁
M = Σ Type₀ is-finite

data S : Set where
  ZERO  : S
  ONE   : S
  PLUS  : S → S → S
  TIMES : S → S → S
\end{code}}

\begin{figure}[h]
\begin{alignat*}{3}
id\!\!\leftrightarrow&:\tau&&\leftrightarrow\tau&&:id\!\!\leftrightarrow\\
unite_+l&:\mathbb{0}\oplus\tau&&\leftrightarrow\tau&&:uniti_+l\\
unite_+r&:\tau\oplus\mathbb{0}&&\leftrightarrow\tau&&:uniti_+r\\
swap_+&:\tau_1\oplus\tau_2&&\leftrightarrow\tau_2\oplus\tau_1&&:swap_+\\
\end{alignat*}
\caption{Level 1 Programs (equivalences) in $\Pi$}
\end{figure}

\AgdaHide{
\begin{code}
data _⟷_ : S → S → Set where
  unite₊l : {t : S} → PLUS ZERO t ⟷ t
  swap₊   : {t₁ t₂ : S} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : S} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  unite⋆l  : {t : S} → TIMES ONE t ⟷ t
  swap⋆   : {t₁ t₂ : S} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : S} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  absorbr : {t : S} → TIMES ZERO t ⟷ ZERO
  dist    : {t₁ t₂ t₃ : S} → TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  id⟷    : {t : S} → t ⟷ t
  1!        : {t₁ t₂ : S} → t₁ ⟷ t₂ → t₂ ⟷ t₁
  _◎_     : {t₁ t₂ t₃ : S} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : S} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : S} → 
              (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

\end{code}}

For example, recall that the Boolean data type can be encoded as $\mathbb{1}+\mathbb{1}$. Negation, which sends \AgdaInductiveConstructor{true} to \AgdaInductiveConstructor{false} and vice versa, is an equivalence. We may define it in many ways---we give two below.

\AgdaHide{
\begin{code}
𝟚 : S
𝟚 = PLUS ONE ONE
\end{code}}

\begin{code}
NOT₁ : 𝟚 ⟷ 𝟚
NOT₁ = swap₊

NOT₂ : 𝟚 ⟷ 𝟚
NOT₂ = id⟷ ◎ (swap₊ ◎ id⟷)
\end{code}

Furthermore, one can ask whether two equivalences are extensionally equal. $\Pi$ then includes a language which encodes such proofs, shown below.

\AgdaHide{
\begin{code}
data _⇔_ : {t₁ t₂ : S} → (t₁ ⟷ t₂) → (t₁ ⟷ t₂) → Set where
  id⇔     : {t₁ t₂ : S} {c : t₁ ⟷ t₂} → c ⇔ c
  2! : {t₁ t₂ : S} {c₁ c₂ : t₁ ⟷ t₂} → c₁ ⇔ c₂ → c₂ ⇔ c₁
  _2◎_  : {t₁ t₂ : S} {c₁ c₂ c₃ : t₁ ⟷ t₂} → 
         (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
  assoc◎l : {t₁ t₂ t₃ t₄ : S} {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₃ ⟷ t₄} →
          (c₁ ◎ (c₂ ◎ c₃)) ⇔ ((c₁ ◎ c₂) ◎ c₃)
  idl◎l   : {t₁ t₂ : S} {c : t₁ ⟷ t₂} → (id⟷ ◎ c) ⇔ c
  idr◎l   : {t₁ t₂ : S} {c : t₁ ⟷ t₂} → (c ◎ id⟷) ⇔ c
  linv◎l  : {t₁ t₂ : S} {c : t₁ ⟷ t₂} → (c ◎ 1! c) ⇔ id⟷
  rinv◎l  : {t₁ t₂ : S} {c : t₁ ⟷ t₂} → (1! c ◎ c) ⇔ id⟷
  _⊡_  : {t₁ t₂ t₃ : S} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₂ ⟷ t₃} {c₃ : t₁ ⟷ t₂} {c₄ : t₂ ⟷ t₃} →
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ◎ c₂) ⇔ (c₃ ◎ c₄)
  resp⊕⇔  : {t₁ t₂ t₃ t₄ : S} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊕ c₂) ⇔ (c₃ ⊕ c₄)
  resp⊗⇔  : {t₁ t₂ t₃ t₄ : S} 
         {c₁ : t₁ ⟷ t₂} {c₂ : t₃ ⟷ t₄} {c₃ : t₁ ⟷ t₂} {c₄ : t₃ ⟷ t₄} → 
         (c₁ ⇔ c₃) → (c₂ ⇔ c₄) → (c₁ ⊗ c₂) ⇔ (c₃ ⊗ c₄)
  sumid : {t₁ t₂ : S} → (id⟷ {t₁} ⊕ id⟷ {t₂}) ⇔ id⟷
  hom⊕◎ : {t₁ t₂ t₃ t₄ t₅ t₆ : S} {c₁ : t₅ ⟷ t₁} {c₂ : t₆ ⟷ t₂}
        {c₃ : t₁ ⟷ t₃} {c₄ : t₂ ⟷ t₄} →
        ((c₁ ◎ c₃) ⊕ (c₂ ◎ c₄)) ⇔ ((c₁ ⊕ c₂) ◎ (c₃ ⊕ c₄))
\end{code}}

As a result, we can write a proof that \AgdaFunction{NOT₁} and \AgdaFunction{NOT₂} are equivalent by cancelling out the instances of \AgdaInductiveConstructor{id⟷}.

\begin{code}
NOT₁⇔NOT₂ : NOT₁ ⇔ NOT₂
NOT₁⇔NOT₂ = 2! (idl◎l 2◎ idr◎l)
\end{code}

Now that we have a language that describes various finite types and their equivalences as well as a model for them in HoTT, we would like to determine whether the language is complete with respect to the model---that is, for every object in the model, there exists an equivalent one in the language and vice versa.

\section{Completeness of Level 0}
Now, we can discuss the completeness of level 0, or types in $\Pi$ with respect to the given model. First, we require translations from the syntax to the model and vice versa. Assume we have the following functions defined.

\begin{code}
-- Converts a type in the syntax
-- to the exact same type in MLTT
#⟦_⟧₀ : S → Type₀
\end{code}
\AgdaHide{
\begin{code}
#⟦ ZERO ⟧₀        = 𝟘
#⟦ ONE  ⟧₀        = 𝟙
#⟦ PLUS  t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ + #⟦ t₂ ⟧₀
#⟦ TIMES t₁ t₂ ⟧₀ = #⟦ t₁ ⟧₀ × #⟦ t₂ ⟧₀
\end{code}}

\begin{code}
-- Computes the number of canonical
-- inhabitants of a type in the syntax
size : S → ℕ
\end{code}
\AgdaHide{
\begin{code}
size ZERO = 0
size ONE  = 1
size (PLUS  t₁ t₂) = add (size t₁) (size t₂)
size (TIMES t₁ t₂) = mult (size t₁) (size t₂)
\end{code}}

\begin{code}
-- Converts an equivalence in the
-- syntax to the same one in HoTT
#⟦_⟧₁ : {X Y : S} → X ⟷ Y → #⟦ X ⟧₀ ≃ #⟦ Y ⟧₀
\end{code}
\AgdaHide{
\begin{code}
#⟦ id⟷ ⟧₁ = ide _
#⟦ unite₊l ⟧₁ = (λ { (i₁ ()); (i₂ x) → x }) ,
  qinv-is-equiv (i₂ , (λ { (i₁ ()); x@(i₂ _) → refl x }) , refl)
#⟦ swap₊ ⟧₁ = (λ { (i₁ x) → i₂ x; (i₂ x) → i₁ x }) ,
  qinv-is-equiv ((λ { (i₁ x) → i₂ x; (i₂ x) → i₁ x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))
#⟦ assocl₊ ⟧₁ = (λ { (i₁ x) → i₁ (i₁ x); (i₂ (i₁ x)) → i₁ (i₂ x); (i₂ (i₂ x)) → i₂ x }) ,
  qinv-is-equiv ((λ { (i₁ (i₁ x)) → i₁ x; (i₁ (i₂ x)) → i₂ (i₁ x); (i₂ x) → i₂ (i₂ x) }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ (i₁ _)) → refl x; x@(i₂ (i₂ _)) → refl x }) ,
    (λ { x@(i₁ (i₁ _)) → refl x; x@(i₁ (i₂ _)) → refl x; x@(i₂ _) → refl x }))
#⟦ unite⋆l ⟧₁ = (λ { (_ , x) → x }) ,
  qinv-is-equiv ((λ x → (0₁ , x)) , (λ { x@(0₁ , _) → refl x }) , refl)
#⟦ swap⋆ ⟧₁ = (λ { (x , y) → (y , x) }) , qinv-is-equiv ((λ { (x , y) → (y , x) }) , refl , refl)
#⟦ assocl⋆ ⟧₁ = (λ { (x , y , z) → ((x , y) , z) }) ,
  qinv-is-equiv ((λ { ((x , y) , z) → x , y , z }) , refl , refl)
#⟦ absorbr ⟧₁ = (λ { (() , _) }) , qinv-is-equiv ((λ ()) , (λ { (() , _) }) , (λ ()))
#⟦ dist ⟧₁ = (λ { (i₁ x , y) → i₁ (x , y); (i₂ x , y) → i₂ (x , y) }) ,
  qinv-is-equiv ((λ { (i₁ (x , y)) → i₁ x , y; (i₂ (x , y)) → i₂ x , y }) ,
    (λ { x@(i₁ _ , _) → refl x; x@(i₂ _ , _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))
{- #⟦ distl ⟧₁ = (λ { (x , i₁ y) → i₁ (x , y); (x , i₂ y) → i₂ (x , y) }) ,
  qinv-is-equiv ((λ { (i₁ (x , y)) → x , i₁ y; (i₂ (x , y)) → x , i₂ y }) ,
    (λ { x@(_ , i₁ _) → refl x; x@(_ , i₂ _) → refl x }) ,
    (λ { x@(i₁ _) → refl x; x@(i₂ _) → refl x }))-}
#⟦ 1! f ⟧₁ = !e #⟦ f ⟧₁
#⟦ f ◎ g ⟧₁ = #⟦ g ⟧₁ ● #⟦ f ⟧₁
#⟦ f ⊕ g ⟧₁ =
  let (f , e) = #⟦ f ⟧₁ in
  let (f⁻¹ , εf , ηf) = hae-is-qinv e in
  let (g , e) = #⟦ g ⟧₁ in
  let (g⁻¹ , εg , ηg) = hae-is-qinv e in
  (λ { (i₁ x) → i₁ (f x); (i₂ x) → i₂ (g x) }) ,
    qinv-is-equiv ((λ { (i₁ y) → i₁ (f⁻¹ y); (i₂ y) → i₂ (g⁻¹ y) }) ,
      (λ { (i₁ x) → ap i₁ (εf x); (i₂ x) → ap i₂ (εg x) }) ,
      (λ { (i₁ y) → ap i₁ (ηf y); (i₂ y) → ap i₂ (ηg y) }))
#⟦ f ⊗ g ⟧₁ =
  let (f , e) = #⟦ f ⟧₁ in
  let (f⁻¹ , εf , ηf) = hae-is-qinv e in
  let (g , e) = #⟦ g ⟧₁ in
  let (g⁻¹ , εg , ηg) = hae-is-qinv e in
  (λ { (a , b) → (f a , g b) }) ,
    qinv-is-equiv ((λ { (c , d) → (f⁻¹ c , g⁻¹ d) }) ,
      (λ { (a , b) → pair= (εf a , εg b) }) ,
      (λ { (c , d) → pair= (ηf c , ηg d) }))
\end{code}}

In order to write the translation into the model, we need a way of relating any type in the semiring $T$ to $El(n)$ where $n = size(T)$. Note that the image of $El(n)$ is a subtype of $S$, allowing us to write an analogous function into $S$.

\begin{code}
fromSize : ℕ → S
\end{code}
\AgdaHide{
\begin{code}
fromSize = recℕ S ZERO (λ _ → PLUS ONE)

size+ : (n₁ n₂ : ℕ) → PLUS (fromSize n₁) (fromSize n₂) ⟷ fromSize (add n₁ n₂)
size+ 0         n₂ = unite₊l
size+ (succ n₁) n₂ = 1! assocl₊ ◎ (id⟷ ⊕ size+ n₁ n₂)

size* : (n₁ n₂ : ℕ) → TIMES (fromSize n₁) (fromSize n₂) ⟷ fromSize (mult n₁ n₂)
size* 0         n₂ = absorbr
size* (succ n₁) n₂ = dist ◎ ((unite⋆l ⊕ size* n₁ n₂) ◎ size+ n₂ (mult n₁ n₂))
\end{code}}

We can formalize the relationship between \AgdaFunction{fromSize} and $\AgdaFunction{El}~n$ as follows.

\begin{code}
fromSize=El : {n : ℕ} → #⟦ fromSize n ⟧₀ == El n
\end{code}
\AgdaHide{
\begin{code}
fromSize=El {n} = indℕ (λ n → #⟦ fromSize n ⟧₀ == El n) (refl 𝟘) (λ _ → ap (_+_ 𝟙)) n
\end{code}}

Then, we define \AgdaFunction{canonical}, which converts a type in the semiring to its ``canonical'' form.

\begin{code}
canonical : S → S
canonical = fromSize ∘ size
\end{code}

Here is an example of the action of \AgdaFunction{canonical}:

$$\AgdaFunction{canonical}~((\mathbb{1}+\mathbb{1})\times(\mathbb{1}+\mathbb{1}))\to\mathbb{1}+\mathbb{1}+\mathbb{1}+\mathbb{1}+\mathbb{0}$$

Intuitively, a type is equivalent to its canonical form, allowing us to write a function that constructs an equivalence in the syntax between them (due to Sabry et al).

\begin{code}
normalize : (T : S) → T ⟷ canonical T
\end{code}

\AgdaHide{
\begin{code}
normalize ZERO = id⟷
normalize ONE  = 1! unite₊l ◎ swap₊
normalize (PLUS t₀ t₁) =
  (normalize t₀ ⊕ normalize t₁) ◎ size+ (size t₀) (size t₁) 
normalize (TIMES t₀ t₁) =
  (normalize t₀ ⊗ normalize t₁) ◎ size* (size t₀) (size t₁)
\end{code}}

We can finally write the translation by using the above functions. Note that we use univalence to convert the equivalence between a type and its canonical form to a path. Then, we use \AgdaFunction{◾} to concatenate that with the path given by \AgdaFunction{fromSize=El} where $n = size(T)$ to generate a path of type $T = El(n)$.

\begin{code}
⟦_⟧₀ : S → M
⟦ T ⟧₀ = (#⟦ T ⟧₀ , size T , ∣ ua #⟦ normalize T ⟧₁ ◾ fromSize=El ∣)
\end{code}

This definition is quite complex, so the following figure demonstrates its action as an injection into the model.

\begin{figure}[h]
\centering\includegraphics[width=\textwidth]{../pictures/translation0.png}
\end{figure}

The translation of the model into the syntax is much simpler---since one cannot perform induction on the opaque type in the first component, we must return the next best thing: a conversion of the size in the second component to a type in the syntax.

\begin{code}
⟦_⟧₀⁻¹ : M → S
⟦(T , n , p)⟧₀⁻¹ = fromSize n
\end{code}

We can again view the action of this translation as an injection in the figure below, taking a triple in the model to a canonical form in the syntax.

\begin{figure}[h]
\centering\includegraphics[width=\textwidth]{../pictures/translation0inverse.png}
\end{figure}

We now have the sufficient tools to discuss the completeness of level 0. Let us formalize the statements of completeness we made two sections ago.

\begin{multicols}{2}
\noindent
\begin{align*}
cmpl^0_1:\prod_{T_1:S}&\sum_{T_2:M}T_1\leftrightarrow\llbracket T_2\rrbracket_0^{-1}\\
T&\mapsto(\llbracket T\rrbracket_0, lem_1)
\end{align*}
\columnbreak
\begin{align*}
cmpl^0_2:\prod_{T_1:M}&\sum_{T_2:S}\parallel T_1=\llbracket T_2\rrbracket_0\parallel\\
T&\mapsto(\llbracket T\rrbracket_0^{-1}, lem_2)
\end{align*}
\end{multicols}

By sending each input to their respective translations, we have proof obligations $lem_1:\prod_{T:S}T\leftrightarrow\llbracket\llbracket T\rrbracket_0\rrbracket_0^{-1}$ and $lem_2:\prod_{T:M}\parallel T=\llbracket\llbracket T\rrbracket_0^{-1}\rrbracket_0\parallel$. Intuitively, these each say that going back and forth between the syntax and model (and vice versa) produces an equivalent object---let us prove them. To prove the first lemma, consider the following diagram, which depicts the round trip of applying both translations.

\begin{figure}[h]
\caption{}
\centering\includegraphics[width=\textwidth]{../pictures/coherence0.png}
\end{figure}

It seems that we simply must construct an equivalence between a type in the syntax and its canonical form, in the same way we did for $\llbracket\cdot\rrbracket_0$. 

\begin{code}
lem₁ : (T : S) → T ⟷ ⟦ ⟦ T ⟧₀ ⟧₀⁻¹
lem₁ = normalize
\end{code}

The other direction is a bit more difficult. First, by \ref{finiteTypeIsUniv} and \AgdaFunction{idtoeqv}, we can define a function that converts paths between the first components of a triple in the model to a path between the entire triple.

\begin{code}
induce : {X Y : M} → p₁ X == p₁ Y → X == Y
\end{code}
\AgdaHide{
\begin{code}
induce = p₁ (finite-types-is-univ _ _) ∘ path-to-eqv
\end{code}}

Now, let us observe the round trip of applying both translations diagrammatically---it yields a similar triple but the first component is in canonical form. Precisely by the original path, we may induce a path across both triples by the fact that the first projection is univalent.

\begin{figure}[h]
\caption{}
\centering\includegraphics[width=\textwidth]{../pictures/coherence0inverse.png}
\end{figure}

This allows us to prove \AgdaFunction{lem₂} by induction on the truncated path in the third component of a triple, which by \AgdaFunction{induce}, gives us the necessary result.

\begin{code}
lem₂ : (X : M) → ∥ X == ⟦ ⟦ X ⟧₀⁻¹ ⟧₀ ∥
lem₂ (T , n , p) =
  recTrunc _ (λ p' → ∣ induce (p' ◾ ! fromSize=El) ∣) identify p
\end{code}

\section{Future Work}
We are currently working on completeness results on levels 1 and 2: isomorphisms and coherences. Furthermore, we would like to develop the formal theory surrounding reversible programming. In particular, there is a deep interplay between homotopy theory and reversibility. For example, we do not have a clear perception of reversible programming with \emph{higher inductive types}, HoTT's internalization of homotopy types. Furthermore, we have the following conjecture which gives a topological characterization of our model, in terms of Eilenberg-MacLane (EM) spaces.

\begin{conjecture}[Rose, 2017]
$$M=\bigoplus_{n\in\mathbb{N}}K(S_n, 1)$$
where $S_n$ is a symmetric group
\end{conjecture}

An EM-space $K(G, n)$ has its $n$\textsuperscript{th} homotopy group (group of $n$-paths under concatenation) isomorphic to $G$ and every other one trivial. Thus, this conjecture states that the type of paths upon finite types of all sizes is precisely all symmetric groups with all higher paths being trivial.

\section{Acknowledgements}

\end{AgdaAlign}
\end{document}
