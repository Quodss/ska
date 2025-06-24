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
++  took
  |^  took
  ::
  +$  took  *
  ++  norm
    |=  a=took
    ^-  took
    ?.  ?=([p=took q=took] a)  a
    =.  p.a  ~=(p.a $(a p.a))
    =.  q.a  ~=(q.a $(a q.a))
    ?:  &(!=(0 p.a) ?=(@ p.a) ?=(@ q.a) =(+(p.a) q.a) =(0 (end 0 p.a)))
      (rsh 0 p.a)
    a
  ++  cons
    |=  [a=took b=took]
    ^-  took
    ?:  &(=(~ a) =(~ b))  ~
    ::  [2n 2n+1] --> n
    ::
    ?:  &(!=(0 a) ?=(@ a) ?=(@ b) =(+(a) b) =(0 (end 0 a)))
      (rsh 0 a)
    [a b]
  ::
  ++  int
    |=  [a=took b=took]
    ^-  took
    ?:  |(=(~ a) =(~ b))  ~
    ::
    =/  a1  (norm a)
    =/  b1  (norm b)
    ~?  |(!=(a1 a) !=(b1 b))  %int-norm  ::  shouldn't fire?
    =.  a  a1
    =.  b  b1
    ::
    ?@  a
      ?@  b  ?:(=(a b) a ~)
      =/  a-l  (lsh 0 a)
      =/  a-r  +(a-l)
      =/  l  $(a a-l, b -.b)
      =/  r  $(a a-r, b +.b)
      ?:  &(=(~ l) =(~ r))  ~
      ?:  &(!=(0 l) ?=(@ l) ?=(@ r) =(+(l) r) =(0 (end 0 l)))
        (rsh 0 l)
      [l r]
    ?^  b
      =/  l  $(a -.a, b -.b)
      =/  r  $(a +.a, b +.b)
      ?:  &(=(~ l) =(~ r))  ~
      ?:  &(!=(0 l) ?=(@ l) ?=(@ r) =(+(l) r) =(0 (end 0 l)))
        (rsh 0 l)
      [l r]
    =/  b-l  (lsh 0 b)
    =/  b-r  +(b-l)
    =/  l  $(a -.a, b b-l)
    =/  r  $(a +.a, b b-r)
    ?:  &(=(~ l) =(~ r))  ~
    ?:  &(!=(0 l) ?=(@ l) ?=(@ r) =(+(l) r) =(0 (end 0 l)))
      (rsh 0 l)
    [l r]
  ::
  ++  slot
    |=  [a=took ax=@]
    ^-  took
    ?:  =(0 ax)  !!
    ?:  =(1 ax)  a
    ?~  a  ~
    =^  dir=?(%2 %3)  ax  [(cap ax) (mas ax)]
    =/  [p=took q=took]
      ?^  a  a
      =/  p  (lsh 0 a)
      =/  q  +(p)
      [p q]
    ::
    ?:  ?=(%2 dir)
      $(a p)
    $(a q)
  ::
  ++  edit
    |=  [rec=took ax=@ don=took]
    ^-  took
    ?:  =(1 ax)  don
    =/  [p=took q=took]
      ?^  rec  rec
      ?~  rec  [~ ~]
      =/  p  (lsh 0 rec)
      =/  q  +(p)
      [p q]
    ::
    ?-  (cap ax)
      %2  [$(rec p, ax (mas ax)) q]
      %3  [p $(rec q, ax (mas ax))]
    ==
  --
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
++  source
  |^  source
  ::
  +$  source  (tree (list peon))
  +$  peon  (pair @axis @uxsite)
  ++  norm
    |=  a=source
    ^-  source
    ?~  a  ~
    =.  l.a  ~=(l.a $(a l.a))
    =.  r.a  ~=(r.a $(a r.a))
    ?:  =([~ ~ ~] a)  ~
    a
  ::
  ++  cons
    |=  [a=source b=source]
    ^-  source
    ?:  &(=(~ a) =(~ b))  ~
    [~ a b]
  ::
  ++  uni
    |=  [a=source b=source]
    ^-  source
    ?~  a  b
    ?~  b  a
    =-  ?:  =([~ ~ ~] -)  ~&  %uni-norm  ~  -  ::  debug check; shouldn't be necessary if source is normalized?
    :+  ~(tap in (~(gas in (~(gas in *(set (pair @axis @uxsite))) n.a)) n.b))
      $(a l.a, b l.b)
    $(a r.a, b r.b)
  ::
  ++  mask
    |=  [src=source cap=cape]
    ^-  source
    ::
    =;  out
      =/  out1  (norm out)
      ~?  !=(out out1)  %mask-norm    ::  should not fire?
      out1
    ::
    ?:  ?=(%| cap)  ~
    ?:  ?=(%& cap)  src
    ?~  src  ~
    =/  l  $(src l.src, cap -.cap)
    =/  r  $(src r.src, cap +.cap)
    ?:  &(=(~ n.src) =(~ l) =(~ r))  ~
    [n.src l r]
  ::
  ++  slot
    |=  [src=source ax=@]
    ^-  source
    ?:  =(1 ax)  src
    =/  rev  1
    =|  acc=(list (pair @ (list peon)))
    |-  ^-  source
    =+  [n l r]=?@(src [~ ~ ~] src)
    ?.  =(1 ax)
      ?-  (cap ax)
        %2  $(ax (mas ax), src l, acc [[rev n] acc], rev (peg rev 2))
        %3  $(ax (mas ax), src r, acc [[rev n] acc], rev (peg rev 3))
      ==
    ::  rev == ax input
    ::
    =.  n
      %+  roll  acc
      |:  [[ax=*@ l=*(list peon)] out=n]
      ^+  n
      ?:  =(~ l)  out
      =/  rel  (hub ax rev)
      %+  roll  l
      |:  [p=*peon out=out]
      [p(p (peg p.p rel)) out]
    ::
    ?:  ?&(?=(~ n) ?=(~ l) ?=(~ r))  ~
    [n l r]
  ::
  ++  edit
    |=  [rec=source ax=@ don=source]
    ^-  source
    ?:  =(ax 1)  don
    =-  ?:(=([~ ~ ~] -) ~ -)
    =/  [n=(list peon) l=source r=source]  ?@(rec [~ ~ ~] rec)
    ?-    (cap ax)
        %2
      =/  r=[n=(list peon) l=source r=source]  ?~(r [~ ~ ~] r)
      =.  n.r
        %+  roll  n.r
        |:  [p=*peon out=n.r]
        [p(p (peg p.p 3)) out]
      ::
      [~ $(rec l, ax (mas ax)) r]
    ::
        %3
      =/  l=[n=(list peon) l=source r=source]  ?~(l [~ ~ ~] l)
      =.  n.l
        %+  roll  n.l
        |:  [p=*peon out=n.l]
        [p(p (peg p.p 2)) out]
      ::
      [~ l $(rec r, ax (mas ax))]
    ==
  --
::
::    axis after axis
::
::  computes the remainder of axis {b} when navigating to {a}.
::  (crashes if b is not in a)
::
++  hub
  |=  [a=@ b=@]
  ?<  =(0 a)
  ?<  =(0 b)
  |-  ^-  @
  ?:  =(a 1)  b
  ?>  =((cap a) (cap b))  ::  remove assertion for performance?
  $(a (mas a), b (mas b))
::
+$  sock-anno  [=sock src=source tok=took]
--