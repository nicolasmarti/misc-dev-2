Open Editor.Fundamental.

Require base.
Require State.

Check StateTrans buffer_state.

Definition bufferstatemonad := StateTrans buffer_state.

Open TypeClass.Instance.

Definition Mbufferstatemonad := MStateTrans buffer_state.
Check Mbufferstatemonad.

Close.

Check return ITrue : bufferstatemonad True.

Recursive mapM (M: Type -> Type) (H: Monad M) (A B : Type) (f: A -> M B) (l: list A) [5] : M (list B) :=
   match l with
     | nil ==> return nil
     | conc hd tl ==> do { x <- f hd
       	       	      	 ; xs <- mapM _ _ _ _ f tl
			 ; return(conc x xs)
	              }
.
Implicite mapM [4].

Recursive concatmapM (M: Type -> Type) (H: Monad M) (A B : Type) (f: A -> M (list B)) (l: list A) [5] : M (list B) :=
   match l with
     | nil ==> return nil
     | conc hd tl ==> do { x <- f hd
       	       	      	 ; xs <- concatmapM _ _ _ _ f tl
			 ; return(app x xs)
	              }
.
Implicite concatmapM [4].

Definition getst : bufferstatemonad buffer_state :=
     readstate.
Check getst.

Definition setst st : bufferstatemonad True :=
     writestate st.
Check setst.


Definition test (input: Input) : bufferstatemonad (list Output) :=
do { x <- getst
   ; let (buffer_st y) := x
   ; y <- setst x
   ; return nil 
}.


Definition loop (inputs : list Input) : bufferstatemonad (list Output) :=
    @concatmapM bufferstatemonad _ _ _ test inputs.

Close.
