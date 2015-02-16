||| Utility functions for working with GRL Models.
module GRL.Utils

import GRL.Model

combineGRLs : GModel MODEL -> GModel MODEL -> GModel MODEL
combineGRLs (GRLSpec xs xxs) (GRLSpec ys yys) = GRLSpec (xs++ys) (xxs++yys)

foldGRLS : GModel MODEL -> List (GModel MODEL) -> GModel MODEL
foldGRLS g gs = foldr (\x, y => combineGRLs x y) g gs

-- --------------------------------------------------------------------- [ EOF ]
