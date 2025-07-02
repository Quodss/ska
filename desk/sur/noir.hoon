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
      [%2 p=nomm q=nomm site=@uxsite]         ::  Nock 2
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
    ::  [2n 2n+1] --> n
    ::
    ?:  &(!=(0 p.a) ?=(@ p.a) ?=(@ q.a) =(+(p.a) q.a) =(0 (end 0 p.a)))
      (rsh 0 p.a)
    a
  ++  cons
    |=  [a=took b=took]
    ^-  took
    ?:  &(=(~ a) =(~ b))  ~
    ?:  &(!=(0 a) ?=(@ a) ?=(@ b) =(+(a) b) =(0 (end 0 a)))
      (rsh 0 a)
    [a b]
  ::
  ++  int
    |=  [a=took b=took]
    ^-  took
    ::
    =/  a1  (norm a)
    =/  b1  (norm b)
    ~?  |(!=(a1 a) !=(b1 b))  %int-norm  ::  shouldn't fire?
    =.  a  a1
    =.  b  b1
    ::
    ?:  |(=(~ a) =(~ b))  ~
    ?:  &(?=(@ a) ?=(@ b))  ?:(=(a b) a ~)
    =/  [l-a=took r-a=took]
      ?^  a  a
      =/  l-a  (lsh 0 a)
      [l-a +(l-a)]
    ::
    =/  [l-b=took r-b=took]
      ?^  b  b
      =/  l-b  (lsh 0 b)
      [l-b +(l-b)]
    ::
    (cons $(a l-a, b l-b) $(a r-a, b r-b))
  ::
  ++  slot
    |=  [a=took ax=@]
    ^-  took
    ?:  =(0 ax)  !!
    ?:  =(1 ax)  a
    ?~  a  ~
    ?@  a  (peg a ax)
    ?-  (cap ax)
      %2  $(a -.a, ax (mas ax))
      %3  $(a +.a, ax (mas ax))
    ==
  ::
  ++  edit
    |=  [rec=took ax=@ don=took]
    ^-  took
    ?:  =(1 ax)  don
    =/  [p=took q=took]
      ?^  rec  rec
      ?~  rec  [~ ~]
      =/  p  (lsh 0 rec)
      [p +(p)]
    ::
    %-  cons
    ?-  (cap ax)
      %2  [$(rec p, ax (mas ax)) q]
      %3  [p $(rec q, ax (mas ax))]
    ==
  ::  relocate new subject sock into old product with `took` 
  ::
  ++  relo-sock
    |=  [sub=sock pro=sock tok=took]
    ^-  sock
    ?~  tok  pro
    ?@  tok  (~(pull so sub) tok)
    =/  l  $(tok -.tok, pro (~(pull so pro) 2))
    =/  r  $(tok +.tok, pro (~(pull so pro) 3))
    (~(knit so l) r)
  ::  relocate new subject provenance into old product with `took` 
  ::
  ++  relo-src
    |=  [sub=source pro=source tok=took]
    ^-  source
    ?~  tok  pro
    ?@  tok  (slot:source sub tok)
    ::   XX performance? defer provenance pushing like in slot?
    ::
    =/  l  $(tok -.tok, pro (slot:source pro 2))
    =/  r  $(tok -.tok, pro (slot:source pro 3))
    (cons:source l r)
  ::  compose captures
  ::
  ::    if a captures s, and b captures a, what b captures from s?
  ::
  ++  comp
    |=  [a=took b=took]
    ^-  took
    ?~  b  ~
    ?@  b  (slot a b)
    (cons $(b -.b) $(b +.b))
  --
::  TODO leave essential to traverse less
::
::  generic info at directly called evalsites
::
+$  evals
  $:
    ::  evalsites <--> sub/fol pairs
    ::
    sites=(map @uxsite [sub=sock fol=*])
    calls=(jar * [site=@uxsite sub=sock])
  ==
::  analysis results
::
+$  results
  $:
    ::  all direct call analysis results
    ::
    every=(map @uxsite [=nomm prod=sock-anno])
    ::  memoized results: finalized, fully direct
    ::  code, minimized subject, full product, subject need
    ::
    memo=(map @uxsite [=nomm less=sock prod=sock-anno want=cape])  ::  XX remove want?
  ==
::  provenance tree: axes of the subject of evalsite
::
++  source
  |^  source
  ::
  +$  source  (tree (list peon))
  +$  peon    [ax=@axis sit=@uxsite]
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
    ::  XX no pushing down? suspicious...
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
    [n.src l r]  ::  preserve root provenance even though l and r might get masked down. dubious
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
      [p(ax (peg ax.p rel)) out]
    ::
    ?:  &(?=(~ n) ?=(~ l) ?=(~ r))  ~
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
        %+  roll  n
        |:  [p=*peon out=n.r]
        [p(ax (peg ax.p 3)) out]
      ::
      [~ $(rec l, ax (mas ax)) ?:(=([~ ~ ~] r) ~ r)]
    ::
        %3
      =/  l=[n=(list peon) l=source r=source]  ?~(l [~ ~ ~] l)
      =.  n.l
        %+  roll  n
        |:  [p=*peon out=n.l]
        [p(ax (peg ax.p 2)) out]
      ::
      [~ ?:(=([~ ~ ~] l) ~ l) $(rec r, ax (mas ax))]
    ==
  ::
  ++  urge
    !.
    =/  unica  |=([@uxsite a=cape b=cape] (~(uni ca a) b))
    |=  [src=source cap=cape]
    ^-  (map @uxsite cape)
    ?:  |(?=(%| cap) ?=(~ src))  ~
    =/  n
      %+  roll  n.src
      |=  [p=peon m=(map @uxsite cape)]
      (~(put by m) sit.p (~(pat ca cap) ax.p))
    ::
    =+  [p q]=?@(cap [& &] cap)
    =/  l  $(src l.src, cap p)
    =/  r  $(src r.src, cap q)
    ((~(uno by ((~(uno by l) r) unica)) n) unica)
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
::  lazily concatenated list
::
++  deep
  |$  [m]
  $%  [%deep p=(deep m) q=(deep m)]
      [%list p=(list m)]
  ==
::
++  dive
  |*  [a=(deep) b=*]
  ^+  a
  ?-  -.a
    %list  a(p [b p.a])
    %deep  a(p $(a p.a))
  ==
::
++  roll-deep
  |*  [a=(deep) g=_=>(~ |=([* *] +<+))]
  |-  ^+  ,.+<+.g
  ?-  -.a
    %list  (roll p.a g)
    %deep  $(a q.a, +<+.g $(a p.a))
  ==
::
++  reel-deep
  |*  [a=(deep) g=_=>(~ |=([* *] +<+))]
  |-  ^+  ,.+<+.g
  ?-  -.a
    %list  (reel p.a g)
    %deep  $(a p.a, +<+.g $(a q.a))
  ==
::
++  peer
  |*  a=(deep)
  $_
  ?>  ?=(%list -.a)
  i.-.p.a
::
++  flatten
  |*  a=(deep)
  ^-  (list (peer a))
  %-  zing
  =|  out=(list (list (peer a)))
  |-  ^-  (list (list (peer a)))
  ?-  -.a
    %list  [p.a out]
    %deep  $(a p.a, out $(a q.a))
  ==
::
++  gave
  |^  gave
  ::
  +$  gave
    $~  [%full ~]
    $^  [gave gave]   ::  cons
    $%  [%full ~]     ::  no capture
        [%hole hole]  ::  capture backedge product
    ==
  ::
  +$  hole  [ax=@axis par=@uxsite kid=@uxsite]
  +$  guess
    $%  [%know p=sock q=hole]
        [%qual p=hole q=hole]
    ==
  ::
  ++  norm
    |=  a=gave
    ^-  gave
    ?@  -.a  a
    =.  -.a  ~=(-.a $(a -.a))
    =.  +.a  ~=(+.a $(a +.a))
    ?:  ?=([[%full ~] %full ~] a)  [%full ~]
    a
  ::
  ++  cons
    |=  [a=gave b=gave]
    ^-  gave
    ?:  &(?=(%full -.a) ?=(%full -.b))  [%full ~]
    [a b]
  ::
  ++  slot
    |=  [a=gave ax=@]
    ^-  gave
    ?^  -.a
      ?-  (cap ax)
        %2  $(ax (mas ax), a -.a)
        %3  $(ax (mas ax), a +.a)
      ==
    ?:  ?=(%full -.a)  a
    a(ax (peg ax.a ax))
  ::  intersect socks where they don't capture loops
  ::  take known sock over loop capturing, recording the assumption
  ::  two different loop captures: record equality assumption
  ::
  ++  int-uni
    |=  [a=[=sock gav=gave] b=[=sock gav=gave]]
    ^-  [[sock gave] (list guess)]
    =-  [-< `(list guess)`(flatten dip)]
    |-  ^-  [[s=sock g=gave] dip=(deep guess)]
    ::
    =/  gav-a1  (norm gav.a)
    =/  gav-b1  (norm gav.b)
    ~?  |(!=(gav-a1 gav.a) !=(gav-b1 gav.b))  %gave-int-uni-norm
    =.  gav.a  gav-a1
    =.  gav.b  gav-b1
    ::
    !!  
  --
::
+$  sock-anno  [=sock src=source tok=took]
::  mask out parts of the result that are going to be relocated anyway
::
++  mask-relo
  |=  a=sock-anno
  ^-  sock-anno
  =-  [(~(app ca -) sock.a) (mask:source src.a -) tok.a]
  ::  cape of result parts that do not capture the subject
  ::
  |-  ^-  cape
  ?~  tok.a  &
  ?@  tok.a  |
  =/  l  $(tok.a -.tok.a)
  =/  r  $(tok.a +.tok.a)
  ?:  &(?=(@ l) =(l r))  l
  [l r]
--