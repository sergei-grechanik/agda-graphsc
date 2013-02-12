
open import Graphsc.Semantics

module Graphsc.Transformation (semantics : Semantics) where

--import Graphsc.Hypergraph
--import Graphsc.Interpretation
import Graphsc.Fin.Transformation
import Graphsc.Fin.SugarTrans
--open Graphsc.Hypergraph semantics public
--open Graphsc.Interpretation semantics public
open Graphsc.Fin.Transformation semantics public
open Graphsc.Fin.SugarTrans semantics public
