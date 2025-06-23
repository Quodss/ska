/+  *soak
|%
::    Nomm (Nock--)
::
::  [%9 p q] => [%7 q %2 [%0 1] %0 p]
::  [%8 p q] => [%7 [p %0 1] q]  (assert p is a cell)
::
+$  nomm
  $^  [nomm nomm]                             ::  autocons
  $%  [%1 p=*]                                ::  Nock 1
      [%2 p=nomm q=nomm site=@uxsite]        ::  Nock 2
      [%3 p=nomm]                             ::  Nock 3
      [%4 p=nomm]                             ::  Nock 4
      [%5 p=nomm q=nomm]                      ::  Nock 5
      [%6 p=nomm q=nomm r=nomm]               ::  Nock 6
      [%7 p=nomm q=nomm]                      ::  Nock 7
      [%10 p=[p=@ q=nomm] q=nomm]             ::  Nock 10
      [%s11 p=@ q=nomm]                       ::  Nock 11 (static)
      [%d11 p=[p=@ q=nomm] q=nomm]            ::  Nock 11 (dynamic)  XX hit formula info?
      [%12 p=nomm q=nomm]                     ::  "Nock 12"
      [%0 p=@]                                ::  Nock 0
  ==
::  +$  took  $~  ~
::            $@  ?(~ @)
::            [took took]
::  describes what parts of subject are contained in the product
::  ~  new noun/unknown
::  @  subject axis
::  ^  cons
::
+$  took  *
::  generic info at evalsites
::
+$  evals
  $:
    ::  evalsites <--> sub/fol pairs
    ::
    sites=(map @uxsite [sub=sock fol=* out=(unit outcome)])
    calls=(jar * [site=@uxsite sub=sock out=(unit outcome)])
  ==
::  analysis results
::
+$  results  (map @uxsite [=nomm prod=sock-anno])
::  info about an analyzed evalsite:
::    parts of the subject it needs for code
::    generated nomm
::    parts of the subject that ended up being captured in the product
::
+$  outcome
  $:  need=cape
      =nomm
      prod=sock-anno
      =took
  ==
::  provenance tree: axes of the subject of evalsite
::
+$  from-sub  (tree (list (pair @axis @uxsite)))
+$  sock-anno  [=sock src=from-sub tok=took]
--