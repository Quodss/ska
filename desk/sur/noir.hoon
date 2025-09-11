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
  ::    p: call stack
  ::    q: all possible unique transformations from the subject of a call to
  ::    a use site of the noun (next call site for all but last, current
  ::    use site in the formula by last), per call.
  ::
  +$  spring  *
  :: +$  spring
  ::   $~  [%null ~]
  ::   $%  [%null ~]
  ::       [%axis p=@]
  ::       [%cons p=spring q=spring]
  ::   ==
  ::
  +$  source  (lest (lest spring))
  ::
  ++  compat
    |=  [old=spring new=spring]
    !.
    ::  %2  -  don't put, new knows less than old
    ::  %1  -  replace old, new knows more
    ::  %0  -  different knowledge, put new and keep old
    ::
    |-  ^-  @
    ?~  new  %2
    ?:  =(old new)  %2
    ?~  old  %1
    ~+
    ?@  old
      ?@  new  %0
      =/  l  $(old (peg old 2), new -.new)
      ?:  =(0 l)  0
      =/  r  $(old (peg old 3), new +.new)
      ?:  !=(l r)
        ::  either r is 0 or head and tail have different nesting, keep both
        ::  springs
        ::
        0
      ::  same knowledge nesting direction for head and tail
      ::
      l
    ?@  new
      =/  l  $(old -.old, new (peg new 2))
      ?:  =(0 l)  0
      =/  r  $(old +.old, new (peg new 3))
      ?:(!=(l r) 0 l)
    =/  l  $(old -.old, new -.new)
    ?:  =(0 l)  0
    =/  r  $(old +.old, new +.new)
    ?:(!=(l r) 0 l)
  ::
  ++  add-spring
    |=  [new=spring lit=(list spring)]
    ^-  (lest spring)
    :: ~>  %bout
    :: ~<  %slog.[0 %add-spring]
    ?~  lit  [new ~]
    :: =>  ?.  (gte (lent lit) 2.000)  .
    ::     =+  (turn t.lit (curr spring-diff i.lit))
    ::     +
    =|  rem=(list spring)
    =/  old  lit
    =>  .(lit `(list spring)`lit)
    !.
    |-  ^-  (lest spring)
    ?~  lit  [new old]
    =/  c
      :: ~>  %bout
      :: ~<  %slog.[0 %compat]
      (compat i.lit new)
    ::
    ?-  c
      %0  $(lit t.lit, rem [i.lit rem])
      %1  [new (weld rem t.lit)]
      %2  old
      @   !!
    ==
  ::
  ++  add-spring-1
    |=  [new=spring lit=(list spring)]
    ^-  (lest spring)
    :: ~>  %bout
    :: ~<  %slog.[0 %add-spring]
    ?~  lit  [new ~]
    :: =>  ?.  (gte (lent lit) 2.000)  .
    ::     =+  (turn t.lit (curr spring-diff i.lit))
    ::     +
    =|  rem=(list spring)
    =/  old  lit
    =>  .(lit `(list spring)`lit)
    !.
    |-  ^-  (lest spring)
    ?~  lit  [new old]
    =/  c
      :: ~>  %bout
      :: ~<  %slog.[0 %compat]
      (compat i.lit new)
    ::
    ?-  c
      %0  $(lit t.lit, rem [i.lit rem])
      %1  [new (weld rem t.lit)]
      %2  old
      @   !!
    ==
  ::
  ++  mul-springs
    |=  [a=(lest spring) b=(lest spring) g=$-([spring spring] spring)]
    ^-  (lest spring)
    =>  .(a `(list spring)`a, b `(list spring)`b)
    =-  ?~(- !! -)
    %+  roll  a
    |=  [pin-a=spring acc=(list spring)]
    %+  roll  b
    |=  [pin-b=spring acc=_acc]
    =/  pin-c  (g pin-a pin-b)
    (add-spring pin-c acc)
  ::
  ++  mul-springs-1
    |=  [a=(lest spring) b=(lest spring) g=$-([spring spring] spring)]
    ^-  (lest spring)
    :: ~&  [(lent a) (lent b)]
    =>  .(a `(list spring)`a, b `(list spring)`b)
    =-  ?~(- !! -)
    %+  roll  a
    |=  [pin-a=spring acc=(list spring)]
    %+  roll  b
    |=  [pin-b=spring acc=_acc]
    =/  pin-c  (g pin-a pin-b)
    (add-spring-1 pin-c acc)
  ::
  ++  mul-springs-bloat
    |=  [a=(lest spring) b=(lest spring) g=$-([spring spring] spring)]
    ^-  (lest spring)
    =>  .(a `(list spring)`a, b `(list spring)`b)
    =-  ?~(- !! -)
    %+  roll  a
    |=  [pin-a=spring acc=(list spring)]
    %+  roll  b
    |=  [pin-b=spring acc=_acc]
    =/  pin-c  (g pin-a pin-b)
    [pin-c acc]
  ::
  ++  weld-springs
    |=  [a=(list spring) b=(list spring)]
    ^-  (lest spring)
    =-  ?~(- ~[~] -)
    =/  b1  b
    |-  ^-  (list spring)
    ?~  a  b
    =/  b2  (add-spring i.a b1)
    =?  b  !=(b1 b2)  [i.a b]
    $(a t.a)
    :: ~|  [a b]
    :: =-  ?~(- ~[~] -)
    :: =|  acc=(tree (list @))
    :: |^  ^-  (list spring)
    :: ?~  a  b
    :: =/  acc1  !.  (insert i.a acc)
    :: ?:  =(acc acc1)  $(a t.a)
    :: $(a t.a, b [i.a b], acc acc1)
    :: ::
    :: ++  insert
    ::   |=  [a=spring acc=(tree (list @))]
    ::   ^+  acc
    ::   !.
    ::   |-
    ::   ?~  a  acc
    ::   ?~  acc  (grow a)
    ::   ?@  a  acc(n [a n.acc])
    ::   ~+
    ::   acc(l $(acc l.acc, a -.a), r $(acc r.acc, a +.a))
    :: ::
    :: ++  grow
    ::   |=  a=spring
    ::   ^-  (tree (list @))
    ::   ?~  a  ~
    ::   ?@  a  [~[a] ~ ~]
    ::   ~+
    ::   [~ $(a -.a) $(a +.a)]
    :: --
  ::
  ++  turn-spring
    |=  [a=(lest spring) g=$-(spring spring)]
    ^-  (lest spring)
    =>  .(a `(list spring)`a)
    =-  ?~(- !! -)
    %+  roll  a
    |=  [pin-a=spring acc=(list spring)]
    =/  pin-b  (g pin-a)
    (add-spring pin-b acc)
  ::
  ++  cons-spring
    |=  [a=spring b=spring]
    ^-  spring
    ?:  &(?=(~ a) ?=(~ b))  ~
    [a b]
    :: ?:  &(?=(%null -.a) ?=(%null -.b))  null+~
    :: [%cons a b]
  ::
  ++  cons
    |=  [a=source b=source]
    ^-  source
    :_  t.a
    (mul-springs-bloat i.a i.b cons-spring)
  ::
  ++  mask-spring
    |=  cap=cape
    |=  pin=spring
    ^-  spring
    ?:  ?=(%| cap)  ~
    ?:  ?=(%& cap)  pin
    ?~  pin  ~
    ~+
    %+  cons-spring  $(cap -.cap, pin ?@(pin (peg pin 2) -.pin))
    $(cap +.cap, pin ?@(pin (peg pin 3) +.pin))
  ::
  ++  mask
    |=  [src=source cap=cape]
    ^-  source
    :_  t.src
    (turn-spring i.src (mask-spring cap))
  ::
  ++  hole-spring
    |=  ax=@
    |=  pin=spring
    ^-  spring
    ?:  =(ax 1)  ~
    ?~  pin  ~
    =|  tack=(list [c=?(%2 %3) p=spring])
    =>  .(pin `spring`pin)
    |-  ^-  spring
    ?.  =(1 ax)
      ?-  (cap ax)
        %2  $(ax (mas ax), pin (hed pin), tack [2+(tel pin) tack])
        %3  $(ax (mas ax), pin (tel pin), tack [3+(hed pin) tack])
      ==
    =/  out=spring  ~
    |-  ^-  spring
    ?~  tack  out
    ?-  c.i.tack
      %2  $(out (cons-spring out p.i.tack), tack t.tack)
      %3  $(out (cons-spring p.i.tack out), tack t.tack)
    ==
  ::
  ++  hole
    |=  [src=source ax=@]
    ^-  source
    :_  t.src
    (turn-spring i.src (hole-spring ax))
  ::
  ++  push-spring
    |=  ax=@
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?:  =(ax 1)  pin
    |-  ^-  spring
    ?:  =(ax 1)  pin
    ?-  (cap ax)
      %2  [$(ax (mas ax)) ~]
      %3  [~ $(ax (mas ax))]
    ==
  ::
  ++  push
    |=  [src=source ax=@]
    ^-  source
    :_  t.src
    =-  ?~(- !! -)
    (turn i.src (push-spring ax))
  ::
  ++  uni
    |=  [a=source b=source]
    ^-  source
    :_  t.a
    =-  ?~(- !! -)
    :: %+  roll  `(list spring)`i.a
    :: |=  [pin=spring acc=_`(list spring)`i.b]
    :: :: ?:  (lien acc |=(spring (compat +< pin)))  acc
    :: :: [pin acc]
    :: (add-spring pin acc)
    (weld-springs i.a i.b)
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
    :: ?:  ?=(%null -.pin)  null+~
    :: ?:  ?=(%axis -.pin)  pin(p (peg p.pin ax))
    :: ?-  (cap ax)
    ::   %2  $(pin p.pin, ax (mas ax))
    ::   %3  $(pin q.pin, ax (mas ax))
    :: ==
  ::
  ++  slot
    |=  [src=source ax=@]
    ^-  source
    :_  t.src
    (turn-spring i.src (slot-spring ax))
  ::
  ++  edit-spring
    |=  ax=@
    |=  [rec=spring don=spring]
    :: ~&  [rec=rec ax=ax don=don]
    :: =-  ~&(- -)
    ^-  spring
    ?:  =(ax 1)  don
    ?:  &(?=(~ rec) ?=(~ don))  ~
    :: ?:  &(?=(%null -.rec) ?=(%null -.don))  null+~
    =|  tack=(list [c=?(%2 %3) p=spring])
    |-  ^-  spring
    ?.  =(1 ax)
      ?-  (cap ax)
        %2  $(ax (mas ax), rec (hed rec), tack [2+(tel rec) tack])
        %3  $(ax (mas ax), rec (tel rec), tack [3+(hed rec) tack])
      ==
    |-  ^-  spring
    ?~  tack  don
    ?-  c.i.tack
      %2  $(don (cons-spring don p.i.tack), tack t.tack)
      %3  $(don (cons-spring p.i.tack don), tack t.tack)
    ==
  ::
  ++  edit
    edit1
    :: |=  [rec=source ax=@ don=source]
    :: ^-  source
    :: =*  sam  +<
    :: |^  ^-  source
    :: =/  one  (edit1 sam)
    :: =/  two  (edit2 sam)
    :: ?.  (equivalent i.one i.two)
    ::   ~|  i.one
    ::   ~|  i.two
    ::   ~|  [rec=i.rec ax=ax don=i.don]
    ::   !!
    :: one
    :: ::
    :: ++  equivalent
    ::   |=  [a=(list spring) b=(list spring)]
    ::   ^-  ?
    ::   =/  acc-a=(tree (set @))
    ::     =|  acc=(tree (set @))
    ::     |-  ^-  (tree (set @))
    ::     ?~  a  acc
    ::     $(a t.a, acc (insert1 i.a acc))
    ::   ::
    ::   =/  acc-b=(tree (set @))
    ::     =|  acc=(tree (set @))
    ::     |-  ^-  (tree (set @))
    ::     ?~  b  acc
    ::     $(b t.b, acc (insert1 i.b acc))
    ::   ::
    ::   :: ?.  =(acc-a acc-b)
    ::   ::   ~&  (print-tree acc-a)
    ::   ::   ~&  (print-tree acc-b)
    ::   ::   !!
    ::   :: &
    ::   =(acc-a acc-b)
    :: ::
    :: ++  print-tree
    ::   |=  t=(tree (set @))
    ::   ^-  ~
    ::   ?~  t  ~
    ::   ~&  [%n n.t]
    ::   ~&  %l
    ::   =+  $(t l.t)
    ::   ~&  %r
    ::   =+  $(t r.t)
    ::   ~
    :: ::
    :: ++  insert1
    ::   |=  [a=spring acc=(tree (set @))]
    ::   ^+  acc
    ::   ?~  a  acc
    ::   ?~  acc  (grow1 a)
    ::   ?@  a  acc(n (~(put in n.acc) a))
    ::   ~+
    ::   acc(l $(acc l.acc, a -.a), r $(acc r.acc, a +.a))
    :: ::
    :: ++  grow1
    ::   |=  a=spring
    ::   ^-  (tree (set @))
    ::   ?~  a  ~
    ::   ?@  a  [[a ~ ~] ~ ~]
    ::   ~+
    ::   [~ $(a -.a) $(a +.a)]
    :: --
  ::
  ++  edit1
    |=  [rec=source ax=@ don=source]
    ^-  source
    :: ~>  %bout
    :: ~&  %edit-start
    :: ~&  [(lent i.rec) ax (lent i.don)]
    :: ~<  %slog.[0 %edit-done]
    :: :_  t.rec
    :: (mul-springs-1 i.rec i.don (edit-spring ax))
    ::
    ::  mask out edit site, unify with `don` pushed to `ax`
    ::
    =.  rec  (hole rec ax)
    =.  don  (push don ax)
    :_  t.rec
    =-  ?~(- !! -)
    (weld i.rec i.don)
  ::
  ++  edit2
    |=  [rec=source ax=@ don=source]
    ^-  source
    :_  t.rec
    (mul-springs i.rec i.don (edit-spring ax))
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
    :: ?:  ?=(%null -.b)  null+~
    |-  ^-  spring
    ?~  a  ~
    :: ?:  ?=(%null -.a)  null+~
    ~+
    ?@  a  ((slot-spring a) b)
    :: ?:  ?=(%axis -.a)  ((slot-spring p.a) b)
    (cons-spring $(a -.a) $(a +.a))
    :: (cons-spring $(a p.a) $(a q.a))
  ::
  ++  compose
    |=  [a=(lest spring) b=(lest spring)]
    ^-  (lest spring)
    (mul-springs-1 a b compose-spring)
  ::
  ++  spring-diff
    |=  [a=spring b=spring]
    ^-  ~
    =/  answer  (compat a b)
    =-  ~>  %slog.[3 (crip "done diff {<`@ux`(mug a)>} {<`@ux`(mug b)>}")]  -
    =/  rev  1
    |-  ^-  ~
    ?:  =(a b)  ~
    :: ?:  |(?=(%null -.a) ?=(%null -.b))
    ?:  |(?=(~ a) ?=(~ b))
      ~&  [answer=answer where=rev a=a b=b]
      ~
    :: ?:  |(&(?=(%axis -.a) ?=(%cons -.b)) &(?=(%axis -.b) ?=(%cons -.a)))
    ?:  |(&(?=(@ a) ?=(^ b)) &(?=(@ b) ?=(^ a)))
      ~&  [answer=answer where=rev a=a b=b]
      ~
    :: ?:  |(?=(%axis -.a) ?=(%axis -.b))
    ?:  |(?=(@ a) ?=(@ b))
      ~&  [answer=answer where=rev a=a b=b]
      ~
    :: ?>  ?=(%cons -.a)
    :: ?>  ?=(%cons -.b)

    :: ?:  =(p.a p.b)  $(a q.a, b q.b, rev (peg rev 3))
    ?:  =(-.a -.b)  $(a +.a, b +.b, rev (peg rev 3))
    =+  $(a -.a, b -.b, rev (peg rev 2))
    ?:  =(+.a +.b)  ~
    $(a +.a, b +.b, rev (peg rev 3))
  ::
  ++  urge
    =|  out=^urge
    |=  [src=source cap=cape tak=(lest @uxsite)]
    :: ~<  %slog.[0 %urge-done]
    :: ~>  %bout
    |-  ^-  ^urge
    ?:  |(?=(%| cap) ?=([~ ~] i.src))  out
    :: ?:  |(?=(%| cap) ?=([[%null ~] ~] i.src))  out
    =.  out
      =;  need=cape  (jib out i.tak _need |=(c=cape (~(uni ca c) need)))
      %+  roll  `(list spring)`i.src
      |=  [pin=spring acc=cape]
      ?~  pin  acc
      :: ?:  ?=(%null -.pin)  acc
      %-  ~(uni ca acc)
      =>  [pin=`spring`pin cap=`cape`cap ..ca]
      |-  ^-  cape
      ?~  pin  |
      :: ?:  ?=(%null -.pin)  |
      ?:  ?=(%| cap)  |
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
    ?~  t.src  out
    ?~  t.tak  !!
    $(t.src t.t.src, tak t.tak, i.src (compose i.src i.t.src))
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