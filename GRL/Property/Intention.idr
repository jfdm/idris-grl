module GRL.Property.Intention

import public Decidable.Equality

import public Data.AVL.Set
import public Data.Graph.AList
import public Data.List

import GRL.Model
import GRL.DSL
import GRL.Types.Expr
import GRL.Types.Value

import public GRL.Property.Common

-- ---------------------------------------------- [ Intentional Link Insertion ]

-- This section details the combinator for intentional link insertion.
--
-- Correctness/Soundness Properties of an Intentional Link
--
-- 1. The link should use elements that are in the model.
-- 2. The destination cannot have type: Resource
-- 3. The src and destination must not be the same.



-- --------------------------------------------------------------------- [ EOF ]
