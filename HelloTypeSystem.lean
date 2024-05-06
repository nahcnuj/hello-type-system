-- This module serves as the root of the `HelloTypeSystem` library.
-- Import modules here that should be built as part of the library.
import «HelloTypeSystem».Basic
import «HelloTypeSystem».Meta
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
  - ペアノ自然数
  - 算術式
  - 判断（judgement）
  - 導出システム（derivation systems）
    - Nat：ペアノ自然数の加算・乗算
    - CompareNat1--3：ペアノ自然数の比較
    - EvalNatExpr：算術式の評価
    - ReduceNatExpr：算術式の簡約
- メタ定理の証明
  - [導出システムNat](./HelloTypeSystem/Meta/Nat.html)
  - [導出システムCompareNat1--3](./HelloTypeSystem/Meta/CompareNat.html)
  - [導出システムEvalNatExpr](./HelloTypeSystem/Meta/EvalNatExpr.html)
  - [導出システムReduceNatExpr](./HelloTypeSystem/Meta/ReduceNatExpr.html)

## Notation
- $\MV{n},\MV{n_1},\dots$（太字斜体）：メタ変数。特にペアノ自然数の場合はそれに対応する普通の自然数を$n,n_1,\dots$と書く。
- $\Set{PNat},\Set{Expr},\dots$（太字立体）：BNFで定義された構文要素の集合

## References
- 五十嵐淳 著. プログラミング言語の基礎概念, サイエンス社, 2011.7, (ライブラリ情報学コア・テキスト ; 24). 978-4-7819-1285-1. [https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587](https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587)
- 大堀淳 著. プログラミング言語の基礎理論. 新装版, 共立出版, 2019.8. 978-4-320-12450-9. [https://ndlsearch.ndl.go.jp/books/R100000002-I029842615](https://ndlsearch.ndl.go.jp/books/R100000002-I029842615)
- G.ウィンスケル 著ほか. プログラミング言語の形式的意味論入門, 丸善出版, 2023.1. 978-4-621-30763-2. [https://ndlsearch.ndl.go.jp/books/R100000002-I032600297](https://ndlsearch.ndl.go.jp/books/R100000002-I032600297)
-/
