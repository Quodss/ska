/+  *soak
:: =/  check-noir  ~
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
    final=(map @uxsite [less=sock fol=* =nomm])
    ::  non-finalized call analysis results
    ::
    $=  process
    %+  map  @uxsite
    $:  sub=sock
        fol=*
        =nomm
        capture=cape
        prod=sock
        map=spring:source
        area=(unit spot)
    ==
    ::  memoized results: finalized, fully direct
    ::  code, minimized subject for match & for code, full product, provenance
    ::  relocation map
    ::
    $=  memo
    %+  jar  *
    $:  arm=@uvarm
        site=@uxsite
        =nomm
        less-memo=sock
        less-code=sock
        prod=sock
        map=spring:source
        area=(unit spot)
    ==
  ==
::  melo entry: code, subject capture cape, full subject to mask, full product
::
+$  meal  $:  site=@uxsite
              =nomm
              capture=cape
              sub=sock-anno
              prod=sock
              map=spring:source
              area=(unit spot)
          ==
::  urge: evalsite subject requirements
::
+$  urge  (map @uxsite cape)
::  provenance tree: axes of the subject of evalsite
::
++  source
  |^  source
  ::
  +$  source  (tree (list peon))
  +$  spring  (tree (list @axis))
  +$  peon    [ax=@axis sit=@uxsite]
::
  ++  check
    !@  check-noir
      |=  [a=source b=@uxsite]
      ^-  ?
      ?:  =(~ a)  &
      |-  ^-  ?
      ?~  a  |
      ?^  f=(find ~[b] (turn n.a |=(peon sit)))  &
      |($(a l.a) $(a r.a))
    _&
  ::
  ++  sorted
    !@  check-noir
      |=  src=source
      ^-  source
      ?~  src  ~
      ?.  =(n.src (sort n.src |=([a=peon b=peon] (gth sit.a sit.b))))
        ~|  n.src
        !!
      :+  n.src
        $(src l.src)
      $(src r.src)
    same
  ::
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
    ::  debug check; shouldn't be necessary if source is normalized?
    ::
    =-  !@  check-noir
          ?:  =([~ ~ ~] -)  ~&(>>> %uni-norm ~)  -
        -
    =/  n
      ::  XX insertion sort?
      ::
      %+  sort  ~(tap in (~(gas in (~(gas in *(set peon)) n.a)) n.b))
      |=  [a=peon b=peon]
      (gth sit.a sit.b)
    ::
    [n $(a l.a, b l.b) $(a r.a, b r.b)]
  ::
  ++  trim
    !@  check-noir
      |=  [src=source cap=cape]
      ^-  source
      =*  sam  +<
      =/  a
        :: ~>  %bout
        (trim1 sam)
      ::
      =/  b
        :: ~>  %bout
        (trim2 sam)
      ::
      ?.  (eq a b)
        ~|  a
        ~|  b
        ~|  [src cap]
        !!
      a
    trim1
  ::
  ++  trim1
    |=  [src=source cap=cape]
    ^-  source
    %-  sorted
    ?~  src  ~
    ?:  ?=(%| cap)  ~
    ?:  ?=(%& cap)  src
    (cons $(src (hed src), cap -.cap) $(src (tel src), cap +.cap))
  ::
  ++  trim2
    |=  [src=source cap=cape]
    ^-  source
    ::
    =;  out
      =/  out1  (norm out)
      ?.  =(out out1)
        ~|  %mask-norm
        ~|  [src cap]
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
      =?  acc  !=(~ n)  [[rev n] acc]
      %+  cons
        $(rev (peg rev 2), src l, cap -.cap)
      $(rev (peg rev 3), src r, cap +.cap)
    ?:  ?=(%| cap)  ~
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
    %+  reel  l
    |:  [p=*peon out=out]
    [p(ax (peg ax.p rel)) out]
  ::
  ++  slot
    |=  [src=source ax=@]
    ^-  source
    ~|  [src ax]
    %-  sorted
    ?:  =(1 ax)  src
    =/  rev  1
    =|  acc=(list (pair @ (list peon)))
    |-  ^-  source
    =+  [n l r]=?@(src [~ ~ ~] src)
    ?.  =(1 ax)
      =?  acc  !=(~ n)  [[rev n] acc]
      ?-  (cap ax)
        %2  $(ax (mas ax), src l, rev (peg rev 2))
        %3  $(ax (mas ax), src r, rev (peg rev 3))
      ==
    ::  rev == ax input
    ::
    =.  n
      %+  roll  acc
      |:  [[ax=*@ l=*(list peon)] out=n]
      ^+  n
      =/  rel  (hub ax rev)
      %+  reel  l
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
    =/  n-a-check  (sort n.a |=([a=peon b=peon] (gth sit.a sit.b)))
    =/  n-b-check  (sort n.b |=([a=peon b=peon] (gth sit.a sit.b)))
    =/  a-check=?
      |-  ^-  ?
      ?~  n-a-check  &
      ?~  n.a  !!
      ?.  =(sit.i.n.a sit.i.n-a-check)  |
      $(n.a t.n.a, n-a-check t.n-a-check)
    ::
    ?.  a-check
      ~|  n.a
      !!
    =/  b-check=?
      |-  ^-  ?
      ?~  n-b-check  &
      ?~  n.b  !!
      ?.  =(sit.i.n.b sit.i.n-b-check)  |
      $(n.b t.n.b, n-b-check t.n-b-check)
    ::
    ?.  b-check
      ~|  n.b
      !!
    ?:  !=((silt n.a) (silt n.b))
      ~&  >>>  rev  |
    ?&  
        $(a l.a, b l.b, rev (peg rev 2))
        $(a r.a, b r.b, rev (peg rev 3))
    ==
  ::
  ++  edit
    !@  check-noir
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
    edit3
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
    =?  acc  !=(~ n)  [[rev n] acc]
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
        =/  rel  (hub ax rev)
        %+  reel  l
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
        =/  rel  (hub ax rev)
        %+  reel  l
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
      %+  reel  `(list peon)`n
      |:  [p=*peon out=n.l1]
      [p(ax (peg ax.p 2)) out]
    ::
    =.  n.r1
      %+  reel  `(list peon)`n
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
    %-  sorted
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
    %-  sorted
    ?~  src  ~
    ?:  =(~ n.src)  l.src
    =+  [n lr]=?~(l.src [~ ~ ~] l.src)
    :_  lr
    %+  reel  n.src
    |:  [p=*peon out=n]
    [p(ax (peg ax.p 2)) out]
  ::
  ++  tel
    |=  src=source
    ^-  source
    %-  sorted
    ?~  src  ~
    ?:  =(~ n.src)  r.src
    =+  [n lr]=?~(r.src [~ ~ ~] r.src)
    :_  lr
    %+  reel  n.src
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
    !@  check-noir
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
    urge2
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
      (jib m sit _need |=(c=cape (~(uni ca c) need)))
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
           (jib m sit _need |=(c=cape (~(uni ca c) need)))
    ==
  ::
  ++  route
    |=  [src=source here=@uxsite]
    ^-  spring
    ?~  src  ~
    =/  n  (murn n.src |=(peon ?.(=(sit here) ~ `ax)))
    =/  l  $(src l.src)
    =/  r  $(src r.src)
    ?:  &(=(~ n) =(~ l) =(~ r))  ~
    [n l r]
  ::
  ++  relo
    !@  check-noir
      |=  [src=source pin=spring]
      ^-  source
      =*  sam  +<
      =/  a
        :: ~>  %bout
        (relo1 sam)
      =/  b
        :: ~>  %bout
        (relo2 sam)
      ?>  (eq a b)
      a
    relo2
  ::
  ++  relo1
    |=  [src=source pin=spring]
    ^-  source
    %-  sorted
    ?~  pin  ~
    =/  recur  (cons $(pin l.pin) $(pin r.pin))
    %+  reel  n.pin
    |:  [ax=*@ out=recur]
    (uni (slot src ax) out)
  ::
  ++  relo2
    =|  out=source
    |=  [src=source pin=spring]
    ^-  source
    ?~  pin  out
    =.  out
      %+  reel  n.pin
      |:  [ax=*@ out=out]
      (uni (slot src ax) out)
    ::
    ?~  out  (cons $(pin l.pin) $(pin r.pin))
    =/  l  $(pin l.pin, out l.out)
    =/  r  $(pin r.pin, out r.out)
    ?:  &(=(~ n.out) =(~ l) =(~ r))  ~
    [n.out l r]
  ::
  ++  prune
    =/  c-out=cape  |
    |=  [src=source site=@uxsite cap=cape]
    ^-  [[cape spring] source]
    =<  [[cap pin] src]
    |-  ^-  [[pin=spring src=source] cap=cape]
    ?~  src  [[~ ~] c-out]
    =^  [n-src=(list peon) n-pin=(list @)]  c-out
      =|  l-out=(list @)
      |-  ^-  [[(list peon) (list @)] cape]
      ?~  n.src  [[~ l-out] c-out]
      ?.  =(site sit.i.n.src)  [[n.src l-out] c-out]
      %=  $
        n.src  t.n.src
        l-out  [ax.i.n.src l-out]
        c-out  ?:  ?=(%| cap)  c-out
               (~(uni ca c-out) (~(pat ca cap) ax.i.n.src))
      ==
    ::
    =/  [l-cap=cape r-cap=cape]  ?@(cap [cap cap] cap)
    =^  [l-pin=spring l-src=source]  c-out  $(src l.src, cap l-cap)
    =^  [r-pin=spring r-src=source]  c-out  $(src r.src, cap r-cap)
    :_  c-out
    :-  ?:(&(=(~ n-pin) =(~ l-pin) =(~ r-pin)) ~ [n-pin l-pin r-pin])
    ?:(&(=(~ n-src) =(~ l-src) =(~ r-src)) ~ [n-src l-src r-src])
  --
::
::    axis after axis
::
::  computes the remainder of axis {b} when navigating to {a}.
::  (crashes if b is not in a)
::
++  hub
  |=  [a=@ b=@]
  :: ::  fast (not actually fast?)
  :: ::
  :: =/  out
  ::   :: ~>  %bout
  ::   =/  met-a  (met 0 a)
  ::   =/  met-b  (met 0 b)
  ::   =/  dif  (sub met-b met-a)
  ::   (con (bex dif) (end [0 dif] b))
  :: ::
  :: =-  ?>  =(out -)  out
  ?<  =(0 a)
  ?<  =(0 b)
  |-  ^-  @
  ?:  =(a 1)  b
  ?>  =((cap a) (cap b))
  $(a (mas a), b (mas b))
::  update a value or push a new one
::
++  jib
  |*  [m=(map) k=* v=(trap *) g=$-(* *)]
  ^+  m
  =-  ?^(- u (~(put by m) k $:v))
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