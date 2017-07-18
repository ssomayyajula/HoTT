\documentclass[12pt, letterpaper]{article}

\usepackage[english]{babel}
\usepackage[T1]{fontenc}
%\usepackage{unicode-math}

\usepackage{amsmath}
\usepackage{hyperref}
\usepackage[references, links]{agda}

%
\usepackage{amsthm}
\usepackage{bussproofs}

\setsansfont[Scale=MatchLowercase]{DejaVuSansMono.ttf}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}{Lemma}[section]
\newtheorem{axiom}{Axiom}[section]

\newcommand{\inl}{\textsf{inl}}
\newcommand{\inr}{\textsf{inr}}
\newcommand{\abst}[2]{\lambda #1.~#2}
\newcommand{\refl}[1]{\textsf{refl}_#1}
\newcommand{\funext}{\textsf{funext}}

\title{Completeness of Π}
\author{Siva Somayyajula}
\date{July 2017}

\begin{document}
\maketitle


\begin{abstract}
$\Pi$ is a reversible programming language by Sabry et al. inspired by isomorphisms over finite types in type theory. We give a model for $\Pi$ in a univalent universe of finite types in homotopy type theory. Using properties of \emph{univalent fibrations}, the underlying concept of this model, we give formal proofs in Agda that level zero terms (types) and level one terms (isomorphisms) in $\Pi$ are complete with respect to this model. We also discuss a formalization of completeness for level two terms (coherence between isomorphisms) and the novelty of homotopy type theory in general.
\end{abstract}

\tableofcontents

\section{Introduction}

\subsection{Reversibility}

Reversibility is prevalent in computing applications, giving rise to ad hoc implementations in both hardware and software alike. For example, the Fredkin and Toffoli gates are universal for reversible circuits, and version control systems like \texttt{darcs} are based on \emph{patch theory}, an algebra for file changes. At the software level, this has motivated the development of general-purpose reversible programming languages---Janus, developed in 1982, is such a language with a formally verified interpreter.

While Janus is designed for imperative programming, there has not yet been such an effort for functional programming, whose emphasis on avoiding mutability, amongst other things, is amenable to reversibility. To elaborate, a natural type-theoretic notion of reversibility is given by type isomorphisms i.e. lossless transformations over structured data. Thus, a calculus for such isomorphisms would give rise to a reversible functional programming language. The $\Pi$ programming language introduced by Sabry et al.is precisely that. However, to understand $\Pi$ and its model, we give a brief introduction to type theory and its homotopy-theoretic interpretation.

\subsection{Type Theory}

A type theory is a formal system for \emph{types}, \emph{terms}, and their computational interactions. A helpful analogy to understand type theory at first is to conceptualize types as sets and terms as their elements. Like set theory, type theories have rules governing \emph{type formation} as there are axioms about set construction e.g. the axiom of pairing, but this is where the analogy breaks down. Whereas set theory makes set membership a proposition provable within the system, type theories have a notion of membership external to the language via \emph{typing judgments}: given a type $A$ and a term $a$, one may derive the judgment $a : A$ (pronounced ``$a$ inhabits $A$'') via \emph{term introduction} and \emph{elimination} rules. As a result, terms are also called \emph{inhabitants}, and we will use those terms interchangeably throughout the rest of the paper.

Perhaps the distinguishing feature of type theories are their explicit treatment of computation: computation rules dictate how terms reduce to values. To programming language theorists, type theories formally describe programming languages and computation rules are precisely the structured operational semantics. On the other hand, set theories have no such equivalent concept.

This emphasis on computation has several applications to computer science. First, the type systems of such programming languages as Haskell are based on certain type theories (specifically, System F). Aside from their utility in programming language design, sufficiently sophisticated type theories are suitable as alternative foundations of mathematics to set theory. In fact, Martin-L\"of type theory (MLTT) is the basis of many programs aiming to formalize constructive mathematics. To understand how this is possible, recall that set theories consist of rules governing the behavior of sets as well as an underlying logic to express propositions and their truth. Thus, it remains to show that type theories, under the availiblity of certain type formers, are languages that can express the construction of arbitrary mathematical objects as well as encode propositions as types and act as deductive systems in their own right.

Thus, we will first give a brief introduction to MLTT in Agda, a proof assistant.

\subsection{Martin-L\"of Type Theory}
The basic type formers of MLTT directly correspond to sets:

\begin{center}
\begin{tabular}{ c|c } 
 \hline
 type & set \\
 \hline
 $U$ & universal set\\
 $\mathbb{0}$ & $\emptyset$\\
 $\mathbb{1}$ & singleton\\
 $A + B$ & coproduct $A\sqcup B$\\
 $A\times B$ & $A\times B$\\
 $A\to B$ & function space $B^A$
\end{tabular}
\end{center}

INSERT EXAMPLES USING ALL TYPES HERE

MLTT then introduces \emph{dependent types}, which generalize the function and the Cartesian product types.

\begin{definition}[Dependent types]
Let $A$ be a type and $P:A\to U$ be a type family. The \emph{dependent function} type \texttt{(a : A) → P a} is inhabited by functions $f$ where if $a : A$, then $f(a):P(a)$ i.e. functions whose codomain type varies with their input.

Similarly, the \emph{dependent pair} type $\sum_{a : A}P(a)$ is inhabited by $(a, b)$ where $a : A$ and $b : P(a)$ i.e. pairs where the type of the second component varies with the first component.
\end{definition}

The utility of these type formers is elucidated in the following explanation: while we now have a calculus to express arbitrary mathematical objects, we still lack a deductive system to perform mathematical reasoning. However, due to the \emph{propositions-as-types} principle, these together with the basic types give rise to a logic for constructive mathematics.

\begin{definition}[Propositions-as-types]
Propositions can be encoded as types. If $A$ is such a type, and $a : A$, then $a$ is a constructive proof of the proposition corresponding to $A$. The exact correspondence is given below.

\begin{center}
\begin{tabular}{ c|c } 
 \hline
 type & proposition \\
 \hline
 $\mathbb{0}$ & \bot\\
 type family $P$ & predicate\\
 $A + B$ & $A\lor B$\\
 $A\times B$ & $A\land B$\\
 $A\to B$ & $A\implies B$\\
 $\prod_{a:A}P(a)$ & $\forall_{a\in A}P(a)$\\
 $\sum_{a:A}P(a)$ & $\exists_{a\in A}P(a)$
\end{tabular}
\end{center}

The intuition behind this principle comes from the Brouwer-Heyting-Kolmogorov interpretation of constructive logic, in which constructive proofs are computable objects. For example, a proof of the disjunction $A\lor B$ is either a proof of $A$ given by $i_1(\ldots)$ or a proof of $B$ given by $i_2(\ldots)$. Furthermore, a proof of a universally quantified formula is a computable function that sends an input to evidence that a particular predicate holds on that input.
\end{definition}

INSERT EXAMPLES USING DEPENDENT PROD \& SUM TYPE HERE

The identification of types and propositions mean that proofs are themselves . This is known as \emph{proof-relevant mathematics}, 

\subsection{Homotopy Type Theory}
Our exposition of MLTT lacks a type that expresses \emoh{propositional equality}.

\begin{definition}[Identity type]
For all types $A$ and $a , b : A$, the \emph{identity type} $a = b$ is inhabited by proofs that $a$ and $b$ are equal, called \emph{identifications}.

By definition, its only canonical inhabitant is reflexivity: $\refl{a}:a = a$.
\end{definition}

Writing functions that pattern match on inhabitants of the identity type is precisely the mystery of homotopy type theory and other excursions into intensional and extensional type theory. For our purposes, we

\begin{definition}[PathFrom]
$$PathFrom(x)\triangleq\sum_{y:A}x=y$$
\end{definition}

\begin{definition}[Paulin-Mohring's J]
Given a type family $P:PathFrom(x)\to U$, $J:P(x, \refl{x})&\to\prod_{c:PathFrom(x)}P(c)$ with the following computation rule:
$$J(r, (x, \refl{x}))\mapsto r$$
\end{definition}

Without using other induction principles for the identity type (such as Axiom K), it is impossible to prove \emph{or} disprove within HoTT that inhabitants of the identity type are propositionally equal to reflexivity, a principle which is called \emph{uniqueness of identity proofs} (UIP). In fact, one can only prove that inhabitants of $PathFrom(x)$ are propositionally equal to $(x, \refl{x})$. As a result, this allows us to add so-called nontrivial inhabitants to the identity type via separate inference rules without rendering the system inconsistent.

This peculiar result motivates, for example, the axiom of function extensionality. Given functions $f,g:A\to B$, if one has evidence $\alpha:\prod_{x:A}f(x)=g(x)$, then one has $\funext(\alpha):f=g$. However, the crux of HoTT lies in Voevodsky's univalence axiom, which is an extensionality axiom for \emph{types}. Before we introduce it, we must first define what it means for two types to be equivalent.

\begin{definition}[Quasi-inverse]
A \emph{quasi-inverse} of a function $f:A\to B$ is the following data:
\begin{itemize}
\item $g:B\to A$
\item $\alpha:\prod_{x:A}g(f(x))=x$
\item $\beta:\prod_{x:B}f(g(x))=x$
\end{itemize}
\end{definition}

For the purposes of this paper, we will refer to functions that have quasi-inverses as equivalences, although there are other equivalent notions in type theory.

\begin{definition}[Type equivalence]
Given types $X$ and $Y$, $X\simeq Y$ if there exists a function $f:X\to Y$ that is an equivalence.
\end{definition}

An immediate result is that an equality between types can be converted to an equivalence.

\begin{lemma}[\textsf{idtoeqv}]
Given types $A$ and $B$, there is a term $\textsf{idtoeqv}:A=B&\to A\simeq B$ defined as:
$$\abst{p}{J((\abst{(B , \_)}{A\simeq B}), ide(A), (B, p))}$$
\end{lemma}

\begin{axiom}[Univalence]
\textsf{idtoeqv} is an equivalence.
\end{axiom}

By declaring that \textsf{idtoeqv} has a quasi-inverse, this axiom gives us the following data:

\begin{itemize}
\item $\textsf{ua}:A\simeq B\to A = B$, a function that converts equivalences to paths
\item $\textsf{ua}-\beta:\pi_{f:A\simeq B}\textsf{idtoeqv}(\textsf{ua}(f))=f$
\item $\textsf{ua}-\eta:\pi_{f:A\simeq B}\textsf{ua}(\textsf{idtoeqv}(p))=p$
\end{itemize}

The last two data are called \emph{propositional computation rules}, as they dictate how \textsf{ua} reduces propositionally, outside of the computation rules built into type theory. However, this raises the question: how do terms compute to a normal form in the presence of univalence? This is actually still an open question---for now, homotopy type theory lacks \emph{canonicity}, the guarantee that every well-typed term has a normal (canonical) form.

Before moving onto $\Pi$ and its model, we must establish one last concept and rethink our previous conception of propositions-as-types. 

\begin{definition}[Mere proposition]
A type is a \emph{mere proposition} if all of its inhabitants are propositionally equal. That is, the following type is inhabited:

$$is-prop(A) = \prod_{x,y:A} x == y$$
\end{definition}

\begin{definition}[Propositional truncation]
For a type $A$, its propositional truncation $\shortparallel A\shortparallel$ is described by the following
\begin{itemize}
\item If $a : A$, then $\shortmid a\shortmid:\shortparallel A\shortparallel$
\item $\textsf{identify}:\Pi_{x,y:\shortparallel A\shortparallel} x == y$
\end{itemize}

By $\textsf{identify}$, the propositional truncation of any type is a proposition, hence the name. Truncation ``forgets'' all the information of terms in a type other than inhabitance, 
\end{definition}

\section{Pi}

\section{Univalent Universe of Finite Types}

\subsection{Univalent Fibrations}

An elementary result in homotopy theory is that a path between points $x$ and $y$ in the base space of a fibration induces an equivalence between the fibers over $x$ and $y$. By univalence, this equivalence is a path as well. We formalize this result below.

\begin{theorem}[\textsf{transporteqv}]
For all types $A$ and type families $P : A → U$, given $x, y : A$, there exists a term $\textsf{transporteqv}:\prod_{P:A\to U}x=y\to P(x)≃P(y)$ defined as:
$$\abst{P}{\abst{p}{J((\abst{b}{P(x)≃P(\pi_1(b))}), ide(P(x)), (y, p))}}$$
\end{theorem}

However, asking whether the converse is true gives the following definition.

\begin{definition}[Univalence]
For all types $A$, a type family $P : A → U$ is a \emph{univalent fibration} if $\textsf{transporteqv}(P)$ is an equivalence.
\end{definition}

That is, univalent fibrations come with a quasi-inverse of \textsf{transporteqv} that converts fiberwise paths to paths in the base space. Even though it is rarely the case that any given type family is a univalent fibration, the following theorem characterizes a class of families that are.

\begin{theorem}[Christensen, Rose]
Let $A$ be a type and $P:A\to U$ be a type family. If for all $x : A$, $P(x)$ is a mere proposition, then $P$ is a univalent fibration.
\end{theorem}


\end{document}
