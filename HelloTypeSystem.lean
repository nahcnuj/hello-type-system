-- This module serves as the root of the `HelloTypeSystem` library.
-- Import modules here that should be built as part of the library.
import «HelloTypeSystem».Basic
import «HelloTypeSystem».Derivation
/-!
$\newcommand\Set[1]{\mathbf{#1}}$
$\newcommand\MV[1]{\boldsymbol{#1}}$
$\newcommand\TT[1]{\texttt{#1}}$
$\newcommand\Evals{\mathrel{\Downarrow}}$
$\newcommand\Reduces{\mathrel{\longrightarrow}}$
$\newcommand\MReduces{\mathrel{\longrightarrow^{\\!*}}}$
$\newcommand\DReduces{\mathrel{\longrightarrow_{\\!d}}}$
-/

/-!
# Hello, Type System
Lean 4でプログラミング言語の型システムや意味論に入門するリポジトリです。
## Index
- [諸定義](./HelloTypeSystem/Basic.html)
  - [ペアノ自然数`PNat`](./HelloTypeSystem/Basic.html#HelloTypeSystem.PNat)
  - [算術式`Expr`](./HelloTypeSystem/Basic.html#HelloTypeSystem.Expr)
  - [判断(judgement)](./HelloTypeSystem/Basic.html#HelloTypeSystem.Judgement)
- 導出システム(derivation systems)
  - [`Nat`](./HelloTypeSystem/Derivation/Nat.html#Nat.Derivation)
  - [`CompareNat1`](./HelloTypeSystem/Derivation/CompareNat.html#CompareNat1.Derivation)
  - [`CompareNat2`](./HelloTypeSystem/Derivation/CompareNat.html#CompareNat2.Derivation)
  - [`CompareNat3`](./HelloTypeSystem/Derivation/CompareNat.html#CompareNat3.Derivation)
  - [`EvalNatExpr`](./HelloTypeSystem/Derivation/EvalNatExpr.html#EvalNatExpr.Derivation)
## Notation
- $\MV{n},\MV{n_1},\dots$（太字斜体）：メタ変数。特にペアノ自然数の場合はそれに対応する普通の自然数を$n,n_1,\dots$と書く。
- $\Set{PNat},\Set{Expr},\dots$（太字立体）：BNFで定義された構文要素の集合
## References
- 五十嵐淳 著. プログラミング言語の基礎概念, サイエンス社, 2011.7, (ライブラリ情報学コア・テキスト ; 24). 978-4-7819-1285-1. [https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587](https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587)
- 大堀淳 著. プログラミング言語の基礎理論. 新装版, 共立出版, 2019.8. 978-4-320-12450-9. [https://ndlsearch.ndl.go.jp/books/R100000002-I029842615](https://ndlsearch.ndl.go.jp/books/R100000002-I029842615)
- G.ウィンスケル 著ほか. プログラミング言語の形式的意味論入門, 丸善出版, 2023.1. 978-4-621-30763-2. [https://ndlsearch.ndl.go.jp/books/R100000002-I032600297](https://ndlsearch.ndl.go.jp/books/R100000002-I032600297)
-/
