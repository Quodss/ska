/+  *soak
:: =/  check-noir  ~
|%
::  call label for Nomm 2: indirect call or entry in global
::  code table or arm-local callsite
::
+$  call
  $~  ~
  $@(~ glob)
::
+$  glob
  $%  [%memo p=@uxmemo]
      [%site p=(pair @uvarm @uxsite)]
  ==
+$  glob-atom  @uwglob  ::  more efficient?
++  en-glob
  |=  $=  call
      $%  [%memo p=@uxmemo]
          [%site p=(pair @uvarm @uxsite)]
      ==
  ^-  glob-atom
  ?:  ?=(%memo -.call)  (lsh 0 p.call)
  .+
  %+  lsh  0
  ::  cantor pairing
  ::
  %+  add  q.p.call
  %+  rsh  0
  %+  mul  (add p.call)
  +((add p.call))
::
++  de-glob
  |=  g=glob-atom
  ^-  $%  [%memo p=@uxmemo]
          [%site p=(pair @uvarm @uxsite)]
      ==
  ?:  =(0 (end 0 g))  [%memo (rsh 0 g)]
  =.  g  (rsh 0 g)
  =/  w  p:(sqt (lsh 0 g))
  =/  t  (rsh 0 (mul w +(w)))
  =?  .  (lth g t)
    =.  w  (dec w)
    =.  t  (rsh 0 (mul w +(w)))
    .
  ::
  =/  y  (sub g t)
  =/  x  (sub w y)
  [%site x y]
::    Nomm (Nock--)
::
::  [%9 p q] => [%7 q %2 [%0 1] %0 p]
::  [%8 p q] => [%7 [p %0 1] q]  (assert p is a cell)
::
+$  nomm
  $^  [nomm nomm]                             ::  autocons
  $%  [%1 p=*]                                ::  Nock 1
      [%2 p=nomm q=nomm site=call]            ::  Nock 2
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
::
::  formula registration coordinate: path + axis in the core
::
+$  bell  (pair path @)
::  memoization table entry
::
+$  meme
  $:  idx=@uxmemo
      arm=@uvarm
      site=@uxsite
      fol=*
      code=nomm
      less-memo=sock
      less-code=sock
      prod=sock
      map=(lest spring:source)
      area=(unit spot)
  ==
::  meloization table entry
::
+$  meal
  $:  site=@uxsite
      =nomm
      capture=cape
      sub=sock-anno
      prod=sock
      map=(lest spring:source)
      area=(unit spot)
  ==
::  cross-arm analysis global state
::
+$  long
  $+  long
  $:
    ::  arm index generator
    ::
    arm-gen=@uvarm
  ::::  memo index generator
    ::
    memo-gen=@uxmemo
  ::::  cold state
    ::
    $=  jets
    $:  root=(jug * path)
        core=(jug path sock)
        batt=(jug ^ path)
        ::  [sub fol]  <--> bell bidirectional mapping
        ::
        $=  cole
        $:  call=(map [sock *] bell) 
            back=(jug bell [sub=sock fol=*])
    ==  ==
  ::::  global code table for memoized entries
    ::
    $=  memo
    $:  fols=(jar * meme)
        idxs=(map @uxmemo meme)
        sits=(map [@uvarm @uxsite] meme)
    ==
  ::::  arm-local info
    ::    areas: call target spots
    ::    doors: entry points into arms: either memo hits or a 0x0 code entry
    ::    sites: finalized code entries for non-0x0 sites
    ::
    $=  arms
    $:  areas=(map @uvarm spot)
        doors=(map @uvarm [less=sock fol=* =nomm])
        sites=(map [@uvarm @uxsite] [less=sock fol=* =nomm])
    ==
  ==
::
+$  frond
  %-  deep
  $:  par=@uxsite
      kid=@uxsite
      par-sub=sock
      kid-sub=sock-anno
      kid-tak=(lest @uxsite)
  ==
::
+$  cycle
  $:  entry=@uxsite
      latch=@uxsite
      =frond
      set=(deep @uxsite)
      process=(deep @uxsite)
      melo=(jar * meal)
      hits=(deep [new-tak=(lest @uxsite) new=@uxsite new-sub=sock-anno =meal])
  ==
::
+$  blocklist  (jug @uxsite @uxsite)
::  arm-local analysis state
::
::    site: evalsite index generator
::    cycles:   stack of call graph cycles (aka natural loops aka strongly
::    connected components)
::      entry: top-most entry into a cyclical call graph
::      latch: right-most, bottom-most evalsite of the cycle
::      frond: set of parent-kid pairs of loop assumptions
::             (target of hypothetical backedge, target of the actual edge,
::              subject socks at the par/kid evalsites)
::      set: set of all vertices in the cycle (to delete from want.gen when
::           done)
::      process: same as set but without kids, melo hits and loop entry
::      melo: cycle-local meloization cache
::      hits: melo hits to validate
::
::      When new assumptions are made, we either extend an old cycle, possibly
::      merging multiple predecessor cycles, or add a new one if its
::      finalization does not depend on previous cycles. Thus, when we finish
::      analysis of a site which is recorded as an entry in `cycles`, we only
::      have to check top cycle entry and we can finalize that loop
::      independently of loops deeper in the stack.
::
::      New cycle condition for a parent-kid pair:
::        parent > latch.i.-.cycles (compare site labels)
::      If false, extend top cycle (set latch to kid, entry to
::      min(entry, parent)), then iterate over the rest of the list, 
::      merging if new cycle overlaps with the predecessor
::      (new entry <= previous latch)
::
::    want: evalsite subject requirements of non-finalized evalsites: parts of
::      the subject that are used as code
::
::    what: subject sock of an unfinalized eval
::
::    bars: number of bars for printing
::    block-loop/melo: blocklists for future guesses during retries
::    area: outermost spot in the current eval
::    locals: finalized call entries that were not memoized
::    memo-entry: potential memo hit for the entry point
::    process: map of non-finalized calls
::
+$  short
  $+  short
  $:  long
      here-arm=@uvarm
      site-gen=@uxsite
      cycles=(list cycle)
      want=urge
      bars=@ud
      block-loop=blocklist
      block-melo=(set @uxsite)  ::  set of entries of cycles where we don't meloize
      area=(unit spot)
      locals=(list [site=@uxsite less=sock fol=* =nomm])
      memo-entry=(unit @uxmemo)
      memo-loop-entry=(list (pair @uxsite @uxmemo))
      $=  process
      %+  map  @uxsite
      $:  sub=sock
          fol=*
          =nomm
          capture=cape
          prod=sock
          map=(lest spring:source)
          area=(unit spot)
  ==  ==
::  urge: evalsite subject requirements
::
+$  urge  (map @uxsite cape)
::  provenance tree: axes of the subject of evalsite
::
++  source
  |^  source
  ::  spring: unit of subject transformation
  ::    ~ : fresh noun
  ::    @ : comes from axis
  ::    ^ : cons
  ::    normalization: [~ ~] -> ~
  ::    doesn't normalize [2n 2n+1]
  ::
  ::  source: full provenance info
  ::    all possible unique transformations from the subject of a call to
  ::    a use site of the noun (next call site for all but last, current
  ::    use site in the formula by last), per call.
  ::
  +$  spring  *
  +$  dyad
    $~  [%root ~]
    $%  [%root p=spring]
        [%uni p=(set dyad)]    ::  i | j | k | ...
        [%comp p=dyad q=dyad]  ::  p . q
  :: +$  spring
  ::   $~  [%null ~]
  ::   $%  [%null ~]
  ::       [%axis p=@]
  ::       [%cons p=spring q=spring]
  ::   ==
  ::
  +$  source  (lest dyad)
  ::
  ++  apply-unary
    |=  g=$-(spring spring)
    |=  a=dyad
    =*  this  .
    ^-  dyad
    ?-  -.a
      %root  a(p (g p.a))
      %uni   a(p (~(run in p.a) this))
      %comp  a(p $(a p.a))
    ==
  ::
  ++  mask-spring
    |=  cap=cape
    |=  pin=spring
    ^-  spring
    |-  ^-  spring
    ?~  pin  ~
    ?:  ?=(%| cap)  ~
    ?:  ?=(%& cap)  pin
    ~+
    %+  cons-spring  $(cap -.cap, pin ?@(pin (peg pin 2) -.pin))
    $(cap +.cap, pin ?@(pin (peg pin 3) +.pin))
  ::
  ++  mask
    |=  [src=source cap=cape]
    ^-  source
    :_  t.src
    ^-  dyad
    (apply-unary i.src (mask-spring cap))
  ::
  ++  uni
    |=  [a=source b=source]
    ^-  source
    :_  t.a
    =/  set-a=(set dyad)
      ?:  ?=(%uni -.i.a)  p.i.a
      [i.a ~ ~]
    ::
    =/  set-b=(set dyad)
      ?:  ?=(%uni -.i.b)  p.i.b
      [i.b ~ ~]
    ::
    [%uni (~(uni in set-a) set-b)]
  ::
  ++  cons-spring
    |=  [a=spring b=spring]
    ^-  spring
    ?:  &(=(~ a) =(~ b))  ~
    [a b]
  ::
  ++  hole-spring
    |=  ax=@
    |=  pin=spring
    ^-  spring
    ?:  =(1 ax)  ~
    =|  acc=(list (pair ?(%2 %3) spring))
    |-  ^-  spring
    ?.  |(=(1 ax) =(~ pin))
      ?-  (cap axe)
          %2  $(pin (hed pin), acc [[%2 (tel pin)] acc], axe (mas axe))
          %3  $(one (tel pin), acc [[%3 (hed pin)] acc], axe (mas axe))
      ==
    =/  out=spring  ~
    |-  ^-  spring
    ?~  acc  out
    ?-  p.i.acc
      %2  $(out (cons-spring out q.i.acc), acc t.acc)
      %3  $(out (cons-spring q.i.acc out), acc t.acc)
    ==
  ::
  ++  cons
    |=  [a=source b=source]
    ^-  source
    =.  i.a  (apply-unary i.a (push-spring 2))
    =.  i.b  (apply-unary i.b (push-spring 3))
    (uni a b)
  ::
  ++  slot-spring
    |=  ax=@
    |=  pin=spring
    ^-  spring
    ?:  =(ax 1)  pin
    ?~  pin  ~
    ?@  pin  (peg pin ax)
    ?-  (cap ax)
      %2  $(pin -.pin, ax (mas ax))
      %3  $(pin +.pin, ax (mas ax))
    ==
  ::
  ++  slot
    |=  [src=source ax=@]
    ^-  source
    :_  t.src
    ^-  dyad
    (apply-unary i.src (slot-spring ax))
  ::
  ++  push-spring
    |=  ax=@
    |=  pin=spring
    ^-  spring
    ?:  =(ax 1)  pin
    ?-  (cap ax)
      %2  [$(ax (mas ax)) ~]
      %3  [~ $(ax (mas ax))]
    ==
  ::
  ++  edit
    |=  [rec=source ax=@ don=source]
    ^-  source
    =.  i.rec  (apply-unary i.rec (hole-spring ax))
    =.  i.don  (apply-unary i.rec (push-spring ax))
    (uni rec don)
  ::
  ++  hed
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 2)
    -.pin
    :: ?:  ?=(%null -.pin)  null+~
    :: ?:  ?=(%axis -.pin)  pin(p (peg p.pin 2))
    :: p.pin
  ::
  ++  tel
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?@  pin  (peg pin 3)
    +.pin
    :: ?:  ?=(%null -.pin)  null+~
    :: ?:  ?=(%axis -.pin)  pin(p (peg p.pin 3))
    :: q.pin
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
  ++  compose-spring
    |=  [a=spring b=spring]
    ^-  spring
    ?~  b  ~
    |-  ^-  spring
    ?~  a  ~
    ~+
    ?@  a  ((slot-spring a) b)
    (cons-spring $(a -.a) $(a +.a))
  ::
  ++  compose
    |=  [a=dyad b=dyad]
    ^-  dyad
    [%comp a b]
  ::
  ++  urge
    |=  [src=source cap=cape tak=(lest @uxsite)]
    ^-  urge
    =|  out=^urge
    |-  ^-  urge
    
  ::
  ++  prune-spring
    |=  [pin=spring cap=cape]
    ^-  cape
    ?:  ?=(%| cap)  |
    ?~  pin  |
    :: ?:  ?=(%null -.pin)  |
    ~+
    ?@  pin  (~(pat ca cap) pin)
    :: ?:  ?=(%axis -.pin)  (~(pat ca cap) p.pin)
    =/  [p=cape q=cape]  ?@(cap [& &] cap)
    =/  l  $(pin -.pin, cap p)
    =/  r  $(pin +.pin, cap q)
    :: =/  l  $(pin p.pin, cap p)
    :: =/  r  $(pin q.pin, cap q)
    (~(uni ca l) r)
  ::
  ++  prune
    |=  [src=(list spring) cap=cape]
    ^-  cape
    %+  roll  src
    |=  [pin=spring acc=_`cape`|]
    (~(uni ca acc) (prune-spring pin cap))
  ::
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
++  depf
  |=  n=*
  ^-  @
  ?@  n  0
  +((max $(n -.n) $(n +.n)))
--