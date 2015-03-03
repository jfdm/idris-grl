||| Utility functions for working with GRL Models.
module GRL.Utils

import GRL.Model

combineGRLs : GModel MODEL -> GModel MODEL -> GModel MODEL
combineGRLs (GRLSpec xs xxs) (GRLSpec ys yys) = GRLSpec (xs++ys) (xxs++yys)

foldGRLS : GModel MODEL -> List (GModel MODEL) -> GModel MODEL
foldGRLS g gs = foldr (\x, y => combineGRLs x y) g gs

insertIntoGRL : GModel ty -> GModel MODEL -> GModel MODEL
insertIntoGRL {ty} x g@(GRLSpec es rs) = case ty of
  ELEM => GRLSpec (x :: es) rs
  LINK => GRLSpec es (x::rs)
  MODEL => combineGRLs x g

-- --------------------------------------------------------------------- [ EOF ]
