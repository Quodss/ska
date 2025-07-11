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
::  TODO leave essential to traverse less
::
::  generic info at directly called evalsites
::
::  analysis results
::
+$  results
  $:
    ::  all finalized call analysis results
    ::
    final=(map @uxsite [less=sock =nomm])
    ::  non-finalized call analysis results
    ::
    process=(map @uxsite [=nomm sub=sock])
    ::  memoized results: finalized, fully direct
    ::  code, minimized subject for match & for code, full product
    ::
    $=  memo
    %+  jar  *
    [site=@uxsite =nomm less-memo=sock less-code=sock prod=sock-anno]
  ==
::  melo entry: code, subject capture cape, full subject to mask, full product
::
+$  meal  [site=@uxsite =nomm capture=cape sub=sock-anno prod=sock-anno]
::  urge: evalsite subject requirements
::
+$  urge  (map @uxsite cape)
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
    =-  ?:  =([~ ~ ~] -)  ~&(>>> %uni-norm ~)  -  ::  debug check; shouldn't be necessary if source is normalized?
    :+  ~(tap in (~(gas in (~(gas in *(set (pair @axis @uxsite))) n.a)) n.b))
      $(a l.a, b l.b)
    $(a r.a, b r.b)
  ::
  ++  mask
    |=  [src=source cap=cape stack=(unit (set @uxsite))]
    ^-  source
    =*  sam  +<
    =/  a
      :: ~>  %bout
      (mask1 sam)
    ::
    =/  b
      :: ~>  %bout
      (mask2 sam)
    ::
    ?.  (eq a b)
      ~|  a
      ~|  b
      ~|  [src cap stack]
      !!
    a
  ::
  ++  mask1
    |=  [src=source cap=cape stack=(unit (set @uxsite))]
    ^-  source
    ?~  src  ~
    ?^  cap  (cons $(src (hed src), cap -.cap) $(src (tel src), cap +.cap))
    ?:  ?=(%| cap)  ~
    ?~  stack  src
    |-  ^-  source
    =.  n.src  (skim n.src |=(peon (~(has in u.stack) sit)))
    =/  l  ?~(l.src ~ $(src l.src))
    =/  r  ?~(r.src ~ $(src r.src))
    ?:  &(=(~ n.src) =(~ l) =(~ r))  ~
    [n.src l r]
  ::  mask provenance tree to a cape, with provenance limited to a 
  ::  potentially infinite set of evalsites
  ::
  ++  mask2
    |=  [src=source cap=cape stack=(unit (set @uxsite))]
    ^-  source
    ::
    =;  out
      =/  out1  (norm out)
      ?.  =(out out1)
        ~|  %mask-norm
        ~|  [src cap stack]
        ~|  out1
        ~|  out
        !!
      out1
    ::  shortcut: nothing to mask
    ::
    ?:  =(~ src)  ~
    ::  accumulator to be pushed to a %& cape
    ::
    =|  acc=(list (pair @ (list peon)))
    =/  rev  1
    |-  ^-  source
    ?^  cap
      ::  shortcut: nothing to push, nothing to mask
      ::
      ?:  &(=(~ acc) =(~ src))  ~
      =+  [n l r]=?~(src [~ ~ ~] src)
      =.  acc  [[rev n] acc]
      %+  cons
        $(rev (peg rev 2), src l, cap -.cap)
      $(rev (peg rev 3), src r, cap +.cap)
    ?:  ?=(%| cap)  ~
    ::  filter for provenance on the stack
    ::
    =?  src  ?=(^ stack)
      |-  ^-  source
      ?~  src  ~
      =.  n.src  (skim n.src |=(peon (~(has in u.stack) sit)))
      =/  l  $(src l.src)
      =/  r  $(src r.src)
      ?:  &(=(~ n.src) =(~ l) =(~ r))  ~
      [n.src l r]
    ::  nothing to push
    ::
    ?:  =(~ acc)  src
    ::  push to node list
    ::
    =/  [n=(list peon) lr=[source source]]  ?~(src [~ ~ ~] src)
    =-  ?:  =([~ ~ ~] -)  ~  -
    :_  lr
    %+  roll  acc
    |:  [[ax=*@ l=*(list peon)] out=n]
    ^+  n
    ?:  =(~ l)  out
    =/  rel  (hub ax rev)
    ?~  stack
      %+  roll  l
      |:  [p=*peon out=out]
      [p(ax (peg ax.p rel)) out]
    %+  roll  l
    |:  [p=*peon out=out]
    ?.  (~(has in u.stack) sit.p)  out
    [p(ax (peg ax.p rel)) out]
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
  ::  equality of provenance trees modulo permutation of peons in lists
  ::
  ++  eq
    =/  rev  1
    |=  [a=source b=source]
    ^-  ?
    ?:  |(&(?=(~ a) ?=(^ b)) &(?=(~ b) ?=(^ a)))
      ~&  >>>  rev  |
    ?~  a  &
    ?>  ?=(^ b)
    ?:  !=((silt n.a) (silt n.b))
      ~&  >>>  rev  |
    ?&  
        $(a l.a, b l.b, rev (peg rev 2))
        $(a r.a, b r.b, rev (peg rev 3))
    ==
  ::
  ++  edit
    |=  [rec=source ax=@ don=source]
    ^-  source
    =*  sam  +<
    =/  a
      :: ~>  %bout
      (edit1 sam)
    ::
    =/  b
      :: ~>  %bout
      (edit2 sam)  ::  faster?
    ::
    =/  c
      :: ~>  %bout
      (edit3 sam)  :: even faster?
    ::
    ?.  (eq a b)
      ~|  sam
      ~|  [a b]
      !!
    ?.  (eq b c)
      ~|  sam
      ~|  [b c]
      !!
    a
  ::
  ++  edit1
    |=  [rec=source ax=@ don=source]
    ^-  source
    ?:  =(ax 1)  don
    =/  rev  1
    =|  acc=(list (pair @ (list peon)))
    |-  ^-  source
    ?:  =(1 ax)  don
    =+  [n l r]=?~(rec [~ ~ ~] rec)
    =.  acc  [[rev n] acc]
    %-  cons
    ^-  [source source]
    ?-    (cap ax)
        %2
      :-  $(rec l, ax (mas ax), rev (peg rev 2))
      =.  rev  (peg rev 3)
      =+  [n-r lr-r]=?~(r [~ ~ ~] r)
      =.  n-r
        %+  roll  acc
        |:  [[ax=*@ l=*(list peon)] out=n-r]
        ^+  n-r
        ?:  =(~ l)  out
        =/  rel  (hub ax rev)
        %+  roll  l
        |:  [p=*peon out=out]
        [p(ax (peg ax.p rel)) out]
      ::
      ?:  =([~ ~ ~] [n-r lr-r])  ~
      [n-r lr-r]
    ::
        %3
      :_  $(rec r, ax (mas ax), rev (peg rev 3))
      =.  rev  (peg rev 2)
      =+  [n-l lr-l]=?~(l [~ ~ ~] l)
      =.  n-l
        %+  roll  acc
        |:  [[ax=*@ l=*(list peon)] out=n-l]
        ^+  n-l
        ?:  =(~ l)  out
        =/  rel  (hub ax rev)
        %+  roll  l
        |:  [p=*peon out=out]
        [p(ax (peg ax.p rel)) out]
      ::
      ?:  =([~ ~ ~] [n-l lr-l])  ~
      [n-l lr-l]
    ==
  ::
  ++  edit2
    |=  [rec=source ax=@ don=source]
    ^-  source
    ?:  =(ax 1)  don
    ::  shortcut: nothing to put, nowhere to put
    ::
    ?:  &(=(~ rec) =(~ don))  ~
    =+  [n l r]=?~(rec [~ ~ ~] rec)
    =+  l1=[n l r]=?~(l [~ ~ ~] l)
    =+  r1=[n l r]=?~(r [~ ~ ~] r)
    =.  n.l1
      %+  roll  `(list peon)`n
      |:  [p=*peon out=n.l1]
      [p(ax (peg ax.p 2)) out]
    ::
    =.  n.r1
      %+  roll  `(list peon)`n
      |:  [p=*peon out=n.r1]
      [p(ax (peg ax.p 3)) out]
    ::
    ?-    (cap ax)
        %2
      %+  cons
        $(rec ?:(=([~ ~ ~] l1) ~ l1), ax (mas ax))
      ?:(=([~ ~ ~] r1) ~ r1)
    ::
        %3
      %+  cons
        ?:(=([~ ~ ~] l1) ~ l1)
      $(rec ?:(=([~ ~ ~] r1) ~ r1), ax (mas ax))
    ==
  ::
  ++  edit3
    |=  [rec=source ax=@ don=source]
    ^-  source
    ?:  =(ax 1)  don
    =|  tack=(list [c=?(%2 %3) p=source])
    |-  ^-  source
    ?.  =(1 ax)
      ?-  (cap ax)
        %2  $(ax (mas ax), rec (hed rec), tack [2+(tel rec) tack])
        %3  $(ax (mas ax), rec (tel rec), tack [3+(hed rec) tack])
      ==
    |-  ^-  source
    ?~  tack  don
    ?-  c.i.tack
      %2  $(don (cons don p.i.tack), tack t.tack)
      %3  $(don (cons p.i.tack don), tack t.tack)
    ==
  ::
  ++  hed
    |=  src=source
    ^-  source
    ?~  src  ~
    ?:  =(~ n.src)  l.src
    =+  [n lr]=?~(l.src [~ ~ ~] l.src)
    :_  lr
    %+  roll  n.src
    |:  [p=*peon out=n]
    [p(ax (peg ax.p 2)) out]
  ::
  ++  tel
    |=  src=source
    ^-  source
    ?~  src  ~
    ?:  =(~ n.src)  r.src
    =+  [n lr]=?~(r.src [~ ~ ~] r.src)
    :_  lr
    %+  roll  n.src
    |:  [p=*peon out=n]
    [p(ax (peg ax.p 3)) out]
  ::
  ::  unify urges
  ::
  ++  uni-urge
    |=  [a=^urge b=^urge]
    ^-  ^urge
    %-  (~(uno by a) b)
    =>  ..ca  ^~
    |=  [@uxsite a=cape b=cape]
    (~(uni ca a) b)
  ::
  ++  urge
    :: urge2
    |=  [src=source cap=cape]
    ^-  ^urge
    =*  sam  +<
    =/  a
      :: ~>  %bout
      (urge1 sam)
    ::
    =/  b
      :: ~>  %bout
      (urge2 sam)
    ::
    ?>  =(a b)
    a
  ::  XX performance: make tail recursive?
  ::
  ++  urge1
    |=  [src=source cap=cape]
    ^-  ^urge
    ?:  |(?=(%| cap) ?=(~ src))  ~
    =/  [p=cape q=cape]  ?@(cap [& &] cap)
    ;:  uni-urge
      $(src l.src, cap p)
      $(src r.src, cap q)
    ::
      %+  roll  n.src
      |=  [peon m=^urge]
      =/  need=cape  (~(pat ca cap) ax)
      (jib m sit need |=(c=cape (~(uni ca c) need)))
    ==
  ::
  ++  urge2
    |=  [src=source cap=cape]
    ^-  ^urge
    =|  tel=(list (pair source cape))
    =|  out=^urge
    |-  ^-  ^urge
    ?:  |(?=(%| cap) ?=(~ src))
      ?~  tel  out
      $(src p.i.tel, cap q.i.tel, tel t.tel)
    =/  [p=cape q=cape]  ?@(cap [& &] cap)
    %=  $
      tel  [[r.src q] tel]
      src  l.src
      cap  p
      out  %+  uni-urge  out
           %+  roll  n.src
           |=  [peon m=^urge]
           =/  need=cape  (~(pat ca cap) ax)
           (jib m sit need |=(c=cape (~(uni ca c) need)))
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
  ::  fast (not actually fast?)
  ::
  =/  out
    :: ~>  %bout
    =/  met-a  (met 0 a)
    =/  met-b  (met 0 b)
    =/  dif  (sub met-b met-a)
    (con (bex dif) (end [0 dif] b))
  ::
  =-  ?>  =(out -)  out
  ::  slow
  ::
  :: ~>  %bout
  ?<  =(0 a)
  ?<  =(0 b)
  |-  ^-  @
  ?:  =(a 1)  b
  ?>  =((cap a) (cap b))
  $(a (mas a), b (mas b))
::  update a value or push a new one
::
++  jib
  |*  [m=(map) k=* v=* g=$-(* *)]
  ^+  m
  =-  ?^(- u (~(put by m) k v))
  |-  ^-  (unit _m)
  ?~  m  ~
  ?:  =(k p.n.m)
    `m(q.n (g q.n.m))
  ?:  (gor k p.n.m)
    =/  l  $(m l.m)
    ?~  l  ~
    `m(l u.l)
  =/  r  $(m r.m)
  ?~  r  ~
  `m(r u.r)
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
::  mold builder from deep, cannot safely bunt
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
    $%  [%know p=sock q=hole]  ::  equality to a sock
        [%qual p=hole q=hole]  ::  equality of holes
    ==
  ::
  ++  full  full+~
  ::
  ++  norm
    |=  a=gave
    ^-  gave
    ?@  -.a  a
    =.  -.a  ~=(-.a $(a -.a))
    =.  +.a  ~=(+.a $(a +.a))
    ?:  ?=([[%full ~] %full ~] a)  full
    a
  ::
  ++  cons
    |=  [a=gave b=gave]
    ^-  gave
    ?:  &(?=(%full -.a) ?=(%full -.b))  full
    [a b]
  ::
  ++  slot
    |=  [a=gave ax=@]
    ^-  gave
    ?:  =(ax 1)  a
    ?:  ?=(%full -.a)  a
    ?@  -.a  a(ax (peg ax.a ax))
    ?-  (cap ax)
      %2  $(ax (mas ax), a -.a)
      %3  $(ax (mas ax), a +.a)
    ==
  ::
  ++  hed
    |=  a=gave
    ^-  gave
    ?:  ?=(%full -.a)  full
    ?^  -.a  -.a
    a(ax (lsh 0 ax.a))
  ::
  ++  tel
    |=  a=gave
    ^-  gave
    ?:  ?=(%full -.a)  full
    ?^  -.a  +.a
    a(ax +((lsh 0 ax.a)))
  ::
  ::  intersect socks where they don't capture loops, unify when one of them
  ::  does. Returns intersected-unified sock-gave pair and a list of assumptions
  ::  to be validated.
  ::  
  ::
  ++  int-uni
    |=  [a=[=sock gav=gave] b=[=sock gav=gave]]
    ^-  [[sock gave] (list guess)]
    =-  [[s g] (flatten dip)]
    |-  ^-  [[s=sock g=gave] dip=(deep guess)]
    ::
    =/  gav-a1  (norm gav.a)
    =/  gav-b1  (norm gav.b)
    ~?  >>>  |(!=(gav-a1 gav.a) !=(gav-b1 gav.b))  %gave-int-uni-norm
    =.  gav.a  gav-a1
    =.  gav.b  gav-b1
    ::
    ::  both don't capture loop products: intersect
    ::
    ?:  &(?=(%full -.gav.a) ?=(%full -.gav.b))
      [[(~(purr so sock.a) sock.b) full] list+~]
    ::  both capture: overwrite with the product of latest parent (does it
    ::  matter?), guess equality
    ::  
    ?:  &(?=(%hole -.gav.a) ?=(%hole -.gav.b))
      [?:((gth par.gav.a par.gav.b) a b) list+~[[%qual +.gav.a +.gav.b]]]
    ::  one doesn't capture, another captures: overwrite with known, guess
    ::  that we know the product
    ::
    ?:  &(?=(%full -.gav.a) ?=(%hole -.gav.b))
      [a list+~[[%know sock.a +.gav.b]]]
    ?:  &(?=(%full -.gav.b) ?=(%hole -.gav.a))
      [b list+~[[%know sock.b +.gav.a]]]
    ::  all other cases (at least one cons case): split sock-gaves, decend,
    ::  cons products and guesses
    ::
    =/  l-a=[sock gave]  [~(hed so sock.a) (hed gav.a)]
    =/  r-a=[sock gave]  [~(tel so sock.a) (tel gav.a)]
    =/  l-b=[sock gave]  [~(hed so sock.b) (hed gav.b)]
    =/  r-b=[sock gave]  [~(tel so sock.b) (tel gav.b)]
    =/  l  $(a l-a, b l-b)
    =/  r  $(a r-a, b r-b)
    [[(~(knit so s.l) s.r) (cons g.l g.r)] [%deep dip.l dip.r]]
  ::
  ++  edit
    |=  [rec=gave ax=@ don=gave]
    ^-  gave
    ?:  =(1 ax)  don
    =/  [p=gave q=gave]
      ::  [(slot 2 rec) (slot 3 rec)] inlined
      ::
      ?-  -.rec
        ^      rec
        %full  [full full]
        %hole  [rec(ax (lsh 0 ax.rec)) rec(ax +((lsh 0 ax.rec)))]
      ==
    ::
    %-  cons
    ?-  (cap ax)
      %2  [$(rec p, ax (mas ax)) q]
      %3  [p $(rec q, ax (mas ax))]
    ==
  --
::
+$  sock-anno  [=sock src=source]
--