module Data.RelationProperties

%default total

--  Side note: At the moment, trying to use the 'rel' via the 'using'
--  declaration results in this error for each class:
--    rel does not have a function type (Type)

--using (a:t, b:t, c:t, rel : t -> t -> Type)
using (a:t, b:t, c:t)

  class Reflexive t (rel : t -> t -> Type) where
    reflexive     : rel a a

  class Irreflexive t (rel : t -> t -> Type) where
    irreflexive   : rel a a  -> _|_

  class Symmetric t (rel : t -> t -> Type) where
    symmetric     : rel a b -> rel b a

  class Asymmetric t (rel : t -> t -> Type) where
    asymmetric    : rel a b -> rel b a -> _|_

  class Antisymmetric t (rel : t -> t -> Type) where
    antisymmetric : rel a b -> rel b a -> (a = b)

  class Transitive t (rel : t -> t -> Type) where
    transitive    : rel a b -> rel b c -> rel a c
