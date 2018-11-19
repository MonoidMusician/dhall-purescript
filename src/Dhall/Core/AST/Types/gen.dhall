    let isZero_pred =
            λ(n : Natural)
          → Natural/fold
            n
            { isZero : Bool, pred : Natural }
            (   λ(r : { isZero : Bool, pred : Natural })
              → { isZero = False, pred = if r.isZero then 0 else r.pred + 1 }
            )
            { isZero = True, pred = 0 }

in  let pred = λ(n : Natural) → (isZero_pred n).pred

in  let sub =
            λ(m : Natural)
          → λ(n : Natural)
          → Natural/fold
            n
            (Natural → Natural)
            (λ(f : Natural → Natural) → λ(i : Natural) → f (pred i))
            (λ(i : Natural) → i)
            m

in  let le = λ(m : Natural) → λ(n : Natural) → Natural/isZero (sub m n)

in  let eq = λ(m : Natural) → λ(n : Natural) → le m n && le n m

in  let indexed = λ(t : Type) → { index : Natural, value : t }

in  let newline = "\n"

in  let List/foldl =
            λ(a : Type)
          → λ(l : List a)
          → λ(list : Type)
          → λ(cons : list → a → list)
          → λ(nil : list)
          → List/fold
            a
            (List/reverse a l)
            list
            (λ(a : a) → λ(b : list) → cons b a)
            nil

in  let withSiblings =
          λ(a : Type) → { prev : Optional a, this : a, next : Optional a }

in  let List/withSiblings =
            λ(a : Type)
          → λ(l : List a)
          →     let qd = { next : Optional a, this : a }
            
            in  let st =
                      { next :
                          Optional a
                      , queued :
                          Optional qd
                      , result :
                          List (withSiblings a)
                      }
            
            in  let dequeue =
                        λ(e : Optional a)
                      → λ(s : st)
                      → Optional/fold
                        qd
                        s.queued
                        (List (withSiblings a))
                        (   λ(q : qd)
                          →   [ { prev = e, this = q.this, next = q.next } ]
                            # s.result
                        )
                        s.result
            
            in  let presult =
                      List/fold
                      a
                      l
                      st
                      (   λ(e : a)
                        → λ(s : st)
                        → { next =
                              [ e ] : Optional a
                          , queued =
                              [ { next = s.next, this = e } ] : Optional qd
                          , result =
                              dequeue ([ e ] : Optional a) s
                          }
                      )
                      { next =
                          [] : Optional a
                      , queued =
                          [] : Optional qd
                      , result =
                          [] : List (withSiblings a)
                      }
            
            in  dequeue ([] : Optional a) presult

in  let Functor = { type : Text }

in  let Param = { functor : < F : Functor | I : {} >, index : Text }

in  let is_functor
        : Param → Bool
        =   λ(a : Param)
          → merge { F = λ(_ : Functor) → True, I = λ(_ : {}) → False } a.functor

in  let Const = { name : Text, type : Text }

in  let ADT_arg = < Const : Const | Param : Param >

in  let render_arg
        : Bool → ADT_arg → Text
        =   λ(diffed : Bool)
          → λ(arg : ADT_arg)
          → merge
            { Const =
                λ(const : Const) → const.type
            , Param =
                  λ(arg : Param)
                → merge
                  { F =
                        λ(f : Functor)
                      → "(" ++ f.type ++ (if diffed then "'" else "") ++ " a)"
                  , I =
                      λ(_ : {}) → "a"
                  }
                  arg.functor
            }
            arg

in  let param
        : Text → ADT_arg
        =   λ(ix : Text)
          → < Param =
                { functor = < I = {=} | F : Functor >, index = ix }
            | Const :
                Const
            >

in  let is_param
        : ADT_arg → Bool
        =   λ(arg : ADT_arg)
          → merge
            { Param = λ(_ : Param) → True, Const = λ(_ : Const) → False }
            arg

in  let count_params
        : List ADT_arg → Natural
        =   λ(args : List ADT_arg)
          → List/fold
            ADT_arg
            args
            Natural
            (   λ(arg : ADT_arg)
              → λ(r : Natural)
              → if is_param arg then r + 1 else r
            )
            0

in  let with_param_index
        : List ADT_arg → List { ix : Natural, arg : ADT_arg }
        =   λ(args : List ADT_arg)
          → ( List/foldl
              ADT_arg
              args
              { ix : Natural, values : List { ix : Natural, arg : ADT_arg } }
              (   λ ( r
                    : { ix :
                          Natural
                      , values :
                          List { ix : Natural, arg : ADT_arg }
                      }
                    )
                → λ(arg : ADT_arg)
                → { ix =
                      if is_param arg then r.ix + 1 else r.ix
                  , values =
                      r.values # [ { ix = r.ix, arg = arg } ]
                  }
              )
              { ix = 0, values = [] : List { ix : Natural, arg : ADT_arg } }
            ).values

in  let ADT_case = { args : List ADT_arg, name : Text }

in  let render_ADT =
            λ(l : List Text)
          → ( List/foldl
              Text
              l
              { text : Text, first : Bool }
              (   λ(r : { text : Text, first : Bool })
                → λ(case : Text)
                → { text =
                      r.text ++ (if r.first then " = " else " | ") ++ case
                  , first =
                      False
                  }
              )
              { text = "", first = True }
            ).text

in  let ADT = { cases : List ADT_case, type : Text, index : Text }

in  let nonempty =
            λ(cases : List ADT_case)
          → List/fold
            ADT_case
            cases
            Bool
            (   λ(case : ADT_case)
              → λ(r : Bool)
              →     r
                &&  List/fold
                    ADT_arg
                    case.args
                    Bool
                    (λ(arg : ADT_arg) → λ(r : Bool) → r || is_param arg)
                    False
            )
            True

in  let render_instance =
            λ(instance_prefix : Text)
          → λ(class_name : Text)
          → λ(args : ADT → Text)
          → λ(functions : List (ADT → Text))
          → λ(adt : ADT)
          → List/foldl
            (ADT → Text)
            functions
            Text
            (λ(r : Text) → λ(f : ADT → Text) → r ++ newline ++ f adt)
            (     newline
              ++  "instance "
              ++  instance_prefix
              ++  adt.type
              ++  " :: "
              ++  class_name
              ++  " "
              ++  args adt
              ++  " where"
            )

in  let render_simple_instance =
            λ(instance_prefix : Text)
          → λ(class_name : Text)
          → render_instance instance_prefix class_name (λ(adt : ADT) → adt.type)

in  let render_indexed_instance =
            λ(instance_prefix : Text)
          → λ(class_name : Text)
          → render_instance
            instance_prefix
            class_name
            (λ(adt : ADT) → "(" ++ adt.index ++ ") " ++ adt.type)

in  let render_indexed_derivative_instance =
            λ(instance_prefix : Text)
          → λ(class_name : Text)
          → render_instance
            instance_prefix
            class_name
            (   λ(adt : ADT)
              → "(" ++ adt.index ++ ") " ++ adt.type ++ " " ++ adt.type ++ "'"
            )

in  let build_function =
            λ(iter : Type)
          → λ(start_arg : iter)
          → λ(fold_arg : iter → ADT_arg → iter)
          → λ(finish_arg : ADT_case → { name : Text, result : iter } → Text)
          → λ(adt : ADT)
          →     let fold_case =
                        λ(case : ADT_case)
                      → finish_arg
                        case
                        { name =
                            case.name
                        , result =
                            List/foldl ADT_arg case.args iter fold_arg start_arg
                        }
            
            in  List/fold
                ADT_case
                adt.cases
                Text
                (λ(case : ADT_case) → λ(s : Text) → fold_case case ++ "\n" ++ s)
                ""

in  let build_function2 =
            λ(v : Type)
          → λ(left : Bool)
          → λ(value0 : v)
          → λ(const_case : Natural → v → Const → v)
          → λ(param_case : Natural → v → Param → v)
          → λ(finish : ADT_case → { ix : Natural, value : v } → Text)
          → λ(adt : ADT)
          →     let f =
                        λ(r : v)
                      → λ(arg : { ix : Natural, arg : ADT_arg })
                      → merge
                        { Const =
                            λ(t : Const) → const_case arg.ix r t
                        , Param =
                            λ(a : Param) → param_case arg.ix r a
                        }
                        arg.arg
            
            in  let each_case =
                        λ(case : ADT_case)
                      →       if left
                        
                        then  List/foldl
                              { ix : Natural, arg : ADT_arg }
                              (with_param_index case.args)
                              v
                              (   λ(r : v)
                                → λ(arg : { ix : Natural, arg : ADT_arg })
                                → f r arg
                              )
                              value0
                        
                        else  List/fold
                              { ix : Natural, arg : ADT_arg }
                              (with_param_index case.args)
                              v
                              (   λ(arg : { ix : Natural, arg : ADT_arg })
                                → λ(r : v)
                                → f r arg
                              )
                              value0
            
            in  List/fold
                ADT_case
                adt.cases
                Text
                (   λ(case : ADT_case)
                  → λ(r : Text)
                  →     finish
                        case
                        { ix = count_params case.args, value = each_case case }
                    ++  newline
                    ++  r
                )
                ""

in  let all_bindings_suffixed
        : Text → ADT_case → Text
        =   λ(suffix : Text)
          → λ(case : ADT_case)
          →     case.name
            ++  List/foldl
                { ix : Natural, arg : ADT_arg }
                (with_param_index case.args)
                Text
                (   λ(r : Text)
                  → λ(arg : { ix : Natural, arg : ADT_arg })
                  → merge
                    { Const =
                        λ(t : Const) → r ++ " " ++ t.name ++ suffix
                    , Param =
                          λ(p : Param)
                        → r ++ " " ++ "a" ++ Natural/show arg.ix ++ suffix
                    }
                    arg.arg
                )
                ""

in  let all_bindings = all_bindings_suffixed ""

in  let param_bindings
        : ADT_case → Text
        =   λ(case : ADT_case)
          →     case.name
            ++  List/foldl
                { ix : Natural, arg : ADT_arg }
                (with_param_index case.args)
                Text
                (   λ(r : Text)
                  → λ(arg : { ix : Natural, arg : ADT_arg })
                  → merge
                    { Const =
                        λ(t : Const) → r ++ " _"
                    , Param =
                        λ(p : Param) → r ++ " " ++ "a" ++ Natural/show arg.ix
                    }
                    arg.arg
                )
                ""

in  let map
        : ADT → Text
        = build_function2
          Text
          True
          ""
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r ++ " " ++ c.name)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →     r
              ++  " ("
              ++  (if is_functor p then "map " else "")
              ++  "f a"
              ++  Natural/show ix
              ++  ")"
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            → "  map f (" ++ all_bindings case ++ ") = " ++ case.name ++ r.value
          )

in  let mapWithIndex
        : ADT → Text
        = build_function2
          Text
          True
          ""
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r ++ " " ++ c.name)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →     r
              ++  " ("
              ++  (       if is_functor p
                    
                    then  "mapWithIndex (\\i -> f (" ++ p.index ++ " i))"
                    
                    else  "f " ++ p.index
                  )
              ++  " a"
              ++  Natural/show ix
              ++  ")"
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            →     "  mapWithIndex f ("
              ++  all_bindings case
              ++  ") = "
              ++  case.name
              ++  r.value
          )

in  let foldMap
        : ADT → Text
        = build_function2
          Text
          True
          "mempty"
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →     (if Natural/isZero ix then "" else r ++ " <> ")
              ++  (if is_functor p then "foldMap f " else "f ")
              ++  "a"
              ++  Natural/show ix
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            → "  foldMap f (" ++ param_bindings case ++ ") = " ++ r.value
          )

in  let foldr
        : ADT → Text
        = build_function2
          Text
          False
          "b"
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →       if is_functor p
              
              then  "(foldr f " ++ r ++ " a" ++ Natural/show ix ++ ")"
              
              else  "(f a" ++ Natural/show ix ++ " " ++ r ++ ")"
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            → "  foldr f b (" ++ param_bindings case ++ ") = " ++ r.value
          )

in  let foldl
        : ADT → Text
        = build_function2
          Text
          True
          "b"
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →       if is_functor p
              
              then  "(foldl f " ++ r ++ " a" ++ Natural/show ix ++ ")"
              
              else  "(f " ++ r ++ " a" ++ Natural/show ix ++ ")"
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            → "  foldl f b (" ++ param_bindings case ++ ") = " ++ r.value
          )

in  let foldMapWithIndex
        : ADT → Text
        = build_function2
          Text
          True
          "mempty"
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →     (if Natural/isZero ix then "" else r ++ " <> ")
              ++  (       if is_functor p
                    
                    then  "foldMapWithIndex (\\i -> f (" ++ p.index ++ " i)) "
                    
                    else  "f " ++ p.index ++ " "
                  )
              ++  "a"
              ++  Natural/show ix
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            →     "  foldMapWithIndex f ("
              ++  param_bindings case
              ++  ") = "
              ++  r.value
          )

in  let foldrWithIndex
        : ADT → Text
        = build_function2
          Text
          False
          "b"
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →       if is_functor p
              
              then      "(foldrWithIndex (\\i -> f ("
                    ++  p.index
                    ++  " i)) "
                    ++  r
                    ++  " a"
                    ++  Natural/show ix
                    ++  ")"
              
              else      "(f "
                    ++  p.index
                    ++  " a"
                    ++  Natural/show ix
                    ++  " "
                    ++  r
                    ++  ")"
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            →     "  foldrWithIndex f b ("
              ++  param_bindings case
              ++  ") = "
              ++  r.value
          )

in  let foldlWithIndex
        : ADT → Text
        = build_function2
          Text
          True
          "b"
          (λ(_ : Natural) → λ(r : Text) → λ(c : Const) → r)
          (   λ(ix : Natural)
            → λ(r : Text)
            → λ(p : Param)
            →       if is_functor p
              
              then      "(foldlWithIndex (\\i -> f ("
                    ++  p.index
                    ++  " i)) "
                    ++  r
                    ++  " a"
                    ++  Natural/show ix
                    ++  ")"
              
              else      "(f "
                    ++  p.index
                    ++  " "
                    ++  r
                    ++  " a"
                    ++  Natural/show ix
                    ++  ")"
          )
          (   λ(case : ADT_case)
            → λ(r : { ix : Natural, value : Text })
            →     "  foldlWithIndex f b ("
              ++  param_bindings case
              ++  ") = "
              ++  r.value
          )

in  let traverse_pattern =
            λ(setup : Text)
          → λ(process : Param → Text)
          → build_function2
            Text
            True
            ""
            (   λ(ix : Natural)
              → λ(r : Text)
              → λ(c : Const)
              → r ++ (if Natural/isZero ix then " " else " <@> ") ++ c.name
            )
            (   λ(ix : Natural)
              → λ(r : Text)
              → λ(p : Param)
              →     r
                ++  (if Natural/isZero ix then " <\$> " else " <*> ")
                ++  process p
                ++  "a"
                ++  Natural/show ix
            )
            (   λ(case : ADT_case)
              → λ(r : { ix : Natural, value : Text })
              →       if Natural/isZero r.ix
                
                then      "  "
                      ++  setup
                      ++  " ("
                      ++  all_bindings case
                      ++  ") = pure ("
                      ++  case.name
                      ++  r.value
                      ++  ")"
                
                else      "  "
                      ++  setup
                      ++  " ("
                      ++  all_bindings case
                      ++  ") = "
                      ++  case.name
                      ++  r.value
            )

in  let traverse
        : ADT → Text
        = traverse_pattern
          "traverse f"
          (λ(p : Param) → if is_functor p then "traverse f " else "f ")

in  let sequence
        : ADT → Text
        = traverse_pattern
          "sequence"
          (λ(p : Param) → if is_functor p then "sequence " else "")

in  let traverseWithIndex
        : ADT → Text
        = traverse_pattern
          "traverseWithIndex f"
          (   λ(p : Param)
            →       if is_functor p
              
              then  "traverseWithIndex (\\i -> f (" ++ p.index ++ " i)) "
              
              else  "f " ++ p.index ++ " "
          )

in  let diffWith =
            λ(adt : ADT)
          →     build_function2
                Text
                True
                ""
                (   λ(ix : Natural)
                  → λ(r : Text)
                  → λ(c : Const)
                  →     r
                    ++  " <*> (if "
                    ++  c.name
                    ++  "_l == "
                    ++  c.name
                    ++  "_r then Just "
                    ++  c.name
                    ++  "_l else Nothing)"
                )
                (   λ(ix : Natural)
                  → λ(r : Text)
                  → λ(p : Param)
                  →     r
                    ++  " <*> "
                    ++  (if is_functor p then "(mergeWith " else "Just (")
                    ++  "f a"
                    ++  Natural/show ix
                    ++  "_l a"
                    ++  Natural/show ix
                    ++  "_r)"
                )
                (   λ(case : ADT_case)
                  → λ(r : { ix : Natural, value : Text })
                  →     "  mergeWith f ("
                    ++  all_bindings_suffixed "_l" case
                    ++  ") ("
                    ++  all_bindings_suffixed "_r" case
                    ++  ") = pure "
                    ++  case.name
                    ++  r.value
                )
                adt
            ++  (       if le 2 (List/length ADT_case adt.cases)
                  
                  then  "  mergeWith _ _ _ = Nothing"
                  
                  else  ""
                )

in  let declarate
        : ADT → Text
        =   λ(adt : ADT)
          →     let declarate1 =
                        λ(case : ADT_case)
                      → List/fold
                        (indexed ADT_arg)
                        (List/indexed ADT_arg (List/reverse ADT_arg case.args))
                        Text
                        (   λ(v : indexed ADT_arg)
                          → λ(r : Text)
                          → r ++ " " ++ render_arg False v.value
                        )
                        case.name
            
            in      "data "
                ++  adt.type
                ++  " a"
                ++  render_ADT
                    ( List/fold
                      ADT_case
                      adt.cases
                      (List Text)
                      (   λ(case : ADT_case)
                        → λ(r : List Text)
                        → [ declarate1 case ] # r
                      )
                      ([] : List Text)
                    )

in  let Zipper_arg = < Hole : Param | Param : Param | Const : Const >

in  let Zipper = { origin : Text, ix : Natural, args : List Zipper_arg }

in  let Zippers = List Zipper

in  let render_Zipper_arg =
            λ(arg : Zipper_arg)
          → merge
            { Hole =
                  λ(p : Param)
                →       if is_functor p
                  
                  then  render_arg True < Param = p | Const : Const >
                  
                  else  "{- a -}"
            , Param =
                λ(p : Param) → render_arg False < Param = p | Const : Const >
            , Const =
                λ(c : Const) → render_arg False < Const = c | Param : Param >
            }
            arg

in  let zipper_args_for_ix =
            λ(args : List ADT_arg)
          → λ(index : Natural)
          → List/foldl
            (indexed ADT_arg)
            (List/indexed ADT_arg args)
            (List Zipper_arg)
            (   λ(r : List Zipper_arg)
              → λ(arg : indexed ADT_arg)
              →   r
                # [ merge
                    { Param =
                          λ(p : Param)
                        →       if eq arg.index index
                          
                          then  < Hole = p | Param : Param | Const : Const >
                          
                          else  < Param = p | Hole : Param | Const : Const >
                    , Const =
                          λ(c : Const)
                        → < Const = c | Hole : Param | Param : Param >
                    }
                    arg.value
                  ]
            )
            ([] : List Zipper_arg)

in  let render_zipper_args_for_ix =
            λ(args : List ADT_arg)
          → λ(index : Natural)
          → ( List/foldl
              (indexed ADT_arg)
              (List/indexed ADT_arg args)
              { result : Text, ix : Natural }
              (   λ(r : { result : Text, ix : Natural })
                → λ(arg : indexed ADT_arg)
                → merge
                  { Param =
                        λ(p : Param)
                      → { result =
                                r.result
                            ++  (       if eq arg.index index
                                  
                                  then        if is_functor p
                                        
                                        then  " z"
                                        
                                        else      " {- a"
                                              ++  Natural/show r.ix
                                              ++  " -}"
                                  
                                  else  " a" ++ Natural/show r.ix
                                )
                        , ix =
                            r.ix + 1
                        }
                  , Const =
                        λ(c : Const)
                      → { result = r.result ++ " " ++ c.name, ix = r.ix }
                  }
                  arg.value
              )
              { result = "", ix = 0 }
            ).result

in  let getZippers_case
        : ADT_case → Zippers
        =   λ(case : ADT_case)
          → List/foldl
            (indexed ADT_arg)
            (List/indexed ADT_arg case.args)
            (List Zipper)
            (   λ(r : List Zipper)
              → λ(v : indexed ADT_arg)
              → merge
                { Param =
                      λ(p : Param)
                    →   r
                      # [ { origin =
                              case.name
                          , ix =
                              List/length Zipper r
                          , args =
                              zipper_args_for_ix case.args v.index
                          }
                        ]
                , Const =
                    λ(_ : Const) → r
                }
                v.value
            )
            ([] : List Zipper)

in  let getZippers
        : ADT → Zippers
        =   λ(adt : ADT)
          → List/fold
            ADT_case
            adt.cases
            Zippers
            (λ(case : ADT_case) → λ(r : List Zipper) → getZippers_case case # r)
            ([] : List Zipper)

in  let differentiate
        : ADT → Text
        =   λ(adt : ADT)
          →     let differentiate1 =
                        λ(case : Zipper)
                      →     case.origin
                        ++  Natural/show case.ix
                        ++  List/foldl
                            Zipper_arg
                            case.args
                            Text
                            (   λ(r : Text)
                              → λ(arg : Zipper_arg)
                              → r ++ " " ++ render_Zipper_arg arg
                            )
                            ""
            
            in      "data "
                ++  adt.type
                ++  "' a"
                ++  render_ADT
                    ( List/fold
                      Zipper
                      (getZippers adt)
                      (List Text)
                      (   λ(case : Zipper)
                        → λ(r : List Text)
                        → [ differentiate1 case ] # r
                      )
                      ([] : List Text)
                    )

in  let zipper_ADT
        : ADT → ADT
        =   λ(adt : ADT)
          →     let zipper_ADT1 =
                        λ(case : Zipper)
                      → { name =
                            case.origin ++ Natural/show case.ix
                        , args =
                            List/foldl
                            Zipper_arg
                            case.args
                            (List ADT_arg)
                            (   λ(r : List ADT_arg)
                              → λ(arg : Zipper_arg)
                              →   r
                                # ( merge
                                    { Hole =
                                          λ(p : Param)
                                        → merge
                                          { F =
                                                λ(f : Functor)
                                              → [ < Param =
                                                      { index =
                                                          p.index
                                                      , functor =
                                                          < F =
                                                              { type =
                                                                  f.type ++ "'"
                                                              }
                                                          | I :
                                                              {}
                                                          >
                                                      }
                                                  | Const :
                                                      Const
                                                  >
                                                ]
                                          , I =
                                              λ(_ : {}) → [] : List ADT_arg
                                          }
                                          p.functor
                                    , Param =
                                          λ(p : Param)
                                        → [ < Param = p | Const : Const > ]
                                    , Const =
                                          λ(c : Const)
                                        → [ < Const = c | Param : Param > ]
                                    }
                                    arg
                                  )
                            )
                            ([] : List ADT_arg)
                        }
            
            in  { type =
                    adt.type ++ "'"
                , cases =
                    List/fold
                    Zipper
                    (getZippers adt)
                    (List ADT_case)
                    (   λ(case : Zipper)
                      → λ(r : List ADT_case)
                      → [ zipper_ADT1 case ] # r
                    )
                    ([] : List ADT_case)
                , index =
                    adt.index
                }

in  let upZF
        : ADT → Text
        =   λ(adt : ADT)
          →     let upZF1 =
                        λ(case : Zipper)
                      → List/foldl
                        Zipper_arg
                        case.args
                        { binding : Text, result : Text, ix : Natural }
                        (   λ ( r
                              : { binding : Text, result : Text, ix : Natural }
                              )
                          → λ(arg : Zipper_arg)
                          → merge
                            { Hole =
                                  λ(p : Param)
                                →       if is_functor p
                                  
                                  then  { binding =
                                                r.binding
                                            ++  " a"
                                            ++  Natural/show r.ix
                                        , result =
                                                r.result
                                            ++  " (upZF (a :<-: pure a"
                                            ++  Natural/show r.ix
                                            ++  "))"
                                        , ix =
                                            r.ix + 1
                                        }
                                  
                                  else  { binding =
                                            r.binding ++ " {- a -}"
                                        , result =
                                            r.result ++ " a"
                                        , ix =
                                            r.ix + 1
                                        }
                            , Param =
                                  λ(p : Param)
                                → { binding =
                                      r.binding ++ " a" ++ Natural/show r.ix
                                  , result =
                                      r.result ++ " a" ++ Natural/show r.ix
                                  , ix =
                                      r.ix + 1
                                  }
                            , Const =
                                  λ(c : Const)
                                → { binding =
                                      r.binding ++ " " ++ c.name
                                  , result =
                                      r.result ++ " " ++ c.name
                                  , ix =
                                      r.ix
                                  }
                            }
                            arg
                        )
                        { binding =
                            case.origin ++ Natural/show case.ix
                        , result =
                            case.origin
                        , ix =
                            0
                        }
            
            in      List/foldl
                    Zipper
                    (getZippers adt)
                    Text
                    (   λ(r : Text)
                      → λ(case : Zipper)
                      →     let code = upZF1 case
                        
                        in      r
                            ++  newline
                            ++  "    "
                            ++  code.binding
                            ++  " -> "
                            ++  code.result
                    )
                    "  upZF (a :<-: z) = case extract z of"
                ++  newline

in  let downZF
        : ADT → Text
        =   λ(adt : ADT)
          →     let downZF1 =
                        λ(case : ADT_case)
                      → List/foldl
                        (indexed ADT_arg)
                        (List/indexed ADT_arg case.args)
                        { result : Text, ix : Natural }
                        (   λ(r : { result : Text, ix : Natural })
                          → λ(arg : indexed ADT_arg)
                          → merge
                            { Param =
                                  λ(p : Param)
                                → { result =
                                            if is_functor p
                                      
                                      then      r.result
                                            ++  " (downZF a"
                                            ++  Natural/show r.ix
                                            ++  " <#> _contextZF' (map \\z -> "
                                            ++  case.name
                                            ++  Natural/show r.ix
                                            ++  render_zipper_args_for_ix
                                                case.args
                                                arg.index
                                            ++  "))"
                                      
                                      else      r.result
                                            ++  " (a"
                                            ++  Natural/show r.ix
                                            ++  " :<-: defer \\_ -> "
                                            ++  case.name
                                            ++  Natural/show r.ix
                                            ++  render_zipper_args_for_ix
                                                case.args
                                                arg.index
                                            ++  ")"
                                  , ix =
                                      r.ix + 1
                                  }
                            , Const =
                                  λ(c : Const)
                                → { result =
                                      r.result ++ " " ++ c.name
                                  , ix =
                                      r.ix
                                  }
                            }
                            arg.value
                        )
                        { result = case.name, ix = 0 }
            
            in  List/fold
                ADT_case
                adt.cases
                Text
                (   λ(case : ADT_case)
                  → λ(r : Text)
                  →     let code = downZF1 case
                    
                    in      "  downZF ("
                        ++  all_bindings case
                        ++  ") = "
                        ++  code.result
                        ++  newline
                        ++  r
                )
                ""

in  let ixF
        : ADT → Text
        =   λ(adt : ADT)
          →     let ixF1 =
                        λ(case : Zipper)
                      → List/foldl
                        Zipper_arg
                        case.args
                        { binding : Text, result : Text }
                        (   λ(r : { binding : Text, result : Text })
                          → λ(arg : Zipper_arg)
                          → merge
                            { Hole =
                                  λ(p : Param)
                                →       if is_functor p
                                  
                                  then  { binding =
                                            r.binding ++ " z"
                                        , result =
                                            r.result ++ p.index ++ " (ixF z)"
                                        }
                                  
                                  else  { binding =
                                            r.binding
                                        , result =
                                            r.result ++ p.index
                                        }
                            , Param =
                                  λ(_ : Param)
                                → { binding =
                                      r.binding ++ " _"
                                  , result =
                                      r.result
                                  }
                            , Const =
                                  λ(_ : Const)
                                → { binding =
                                      r.binding ++ " _"
                                  , result =
                                      r.result
                                  }
                            }
                            arg
                        )
                        { binding =
                            case.origin ++ Natural/show case.ix
                        , result =
                            ""
                        }
            
            in  List/fold
                Zipper
                (getZippers adt)
                Text
                (   λ(case : Zipper)
                  → λ(r : Text)
                  →     let code = ixF1 case
                    
                    in      "  ixF ("
                        ++  code.binding
                        ++  ") = "
                        ++  code.result
                        ++  newline
                        ++  r
                )
                ""

in  let derivateType =
            λ(instance_prefix : Text)
          → λ(class_name : Text)
          → λ(type : Text)
          →     "derive instance "
            ++  instance_prefix
            ++  type
            ++  " :: "
            ++  class_name
            ++  " a => "
            ++  class_name
            ++  " ("
            ++  type
            ++  " a)"

in  let derivateFunctor =
            λ(instance_prefix : Text)
          → λ(class_name : Text)
          → λ(type : Text)
          →     "derive instance "
            ++  instance_prefix
            ++  type
            ++  " :: "
            ++  class_name
            ++  " "
            ++  type

in  let instantiate =
            λ(adt : ADT)
          →     let deriv = zipper_ADT adt
            
            in      declarate adt
                ++  newline
                ++  derivateType "eq" "Eq" adt.type
                ++  newline
                ++  derivateType "ord" "Ord" adt.type
                ++  newline
                ++  derivateFunctor "eq1" "Eq1" adt.type
                ++  newline
                ++  derivateFunctor "ord1" "Ord1" adt.type
                ++  newline
                ++  "type "
                ++  adt.type
                ++  "I = "
                ++  adt.index
                ++  newline
                ++  render_simple_instance "functor" "Functor" [ map ] adt
                ++  render_indexed_instance
                    "functorWithIndex"
                    "FunctorWithIndex"
                    [ mapWithIndex ]
                    adt
                ++  render_simple_instance
                    "foldable"
                    "Foldable"
                    [ foldMap, foldl, foldr ]
                    adt
                ++  render_indexed_instance
                    "foldableWithIndex"
                    "FoldableWithIndex"
                    [ foldMapWithIndex, foldlWithIndex, foldrWithIndex ]
                    adt
                ++  render_simple_instance
                    "traversable"
                    "Traversable"
                    [ traverse, sequence ]
                    adt
                ++  render_indexed_instance
                    "traversableWithIndex"
                    "TraversableWithIndex"
                    [ traverseWithIndex ]
                    adt
                ++  render_simple_instance "merge" "Merge" [ diffWith ] adt
                ++  newline
                ++  differentiate adt
                ++  newline
                ++  derivateType "eq" "Eq" deriv.type
                ++  newline
                ++  derivateType "ord" "Ord" deriv.type
                ++  newline
                ++  derivateFunctor "eq1" "Eq1" deriv.type
                ++  newline
                ++  derivateFunctor "ord1" "Ord1" deriv.type
                ++  newline
                ++  render_simple_instance "functor" "Functor" [ map ] deriv
                ++  render_simple_instance
                    "foldable"
                    "Foldable"
                    [ foldMap, foldl, foldr ]
                    deriv
                ++  render_simple_instance
                    "traversable"
                    "Traversable"
                    [ traverse, sequence ]
                    deriv
                ++  render_simple_instance "merge" "Merge" [ diffWith ] deriv
                ++  render_indexed_derivative_instance
                    "container"
                    "Container"
                    [ upZF, downZF ]
                    adt
                ++  render_instance
                    "containerI"
                    "ContainerI"
                    (λ(adt : ADT) → "(" ++ adt.index ++ ") " ++ adt.type ++ "'")
                    [ ixF ]
                    adt

in  let instantiate_all =
            λ(adts : List ADT)
          → List/fold
            ADT
            adts
            Text
            (λ(adt : ADT) → λ(r : Text) → instantiate adt ++ newline ++ r)
            ""

in  let Pair
        : ADT
        = { cases =
              [ { args = [ param "false", param "true" ], name = "Pair" } ]
          , type =
              "Pair"
          , index =
              "Boolean"
          }

in  let Triplet
        : ADT
        = { cases =
              [ { args =
                    [ param "Three1", param "Three2", param "Three3" ]
                , name =
                    "Triplet"
                }
              ]
          , type =
              "Triplet"
          , index =
              "Three"
          }

in  let TextLitF
        : ADT
        = { cases =
              [ { args =
                    [ < Const =
                          { name = "s", type = "String" }
                      | Param :
                          Param
                      >
                    ]
                , name =
                    "TextLit"
                }
              , { args =
                    [ < Const =
                          { name = "s", type = "String" }
                      | Param :
                          Param
                      >
                    , param "zero"
                    , < Param =
                          { functor =
                              < F = { type = "TextLitF" } | I : {} >
                          , index =
                              "one +"
                          }
                      | Const :
                          Const
                      >
                    ]
                , name =
                    "TextInterp"
                }
              ]
          , type =
              "TextLitF"
          , index =
              "Natural"
          }

in  let MergeF
        : ADT
        = { cases =
              [ { name =
                    "MergeF"
                , args =
                    [ param "Three1"
                    , param "Three2"
                    , < Param =
                          { functor =
                              < F = { type = "Maybe" } | I : {} >
                          , index =
                              "const Three3"
                          }
                      | Const :
                          Const
                      >
                    ]
                }
              ]
          , type =
              "MergeF"
          , index =
              "Three"
          }

in  let LetF
        : ADT
        = { cases =
              [ { name =
                    "LetF"
                , args =
                    [ < Const =
                          { type = "String", name = "s" }
                      | Param :
                          Param
                      >
                    , < Param =
                          { functor =
                              < F = { type = "Maybe" } | I : {} >
                          , index =
                              "const Three1"
                          }
                      | Const :
                          Const
                      >
                    , param "Three2"
                    , param "Three3"
                    ]
                }
              ]
          , type =
              "LetF"
          , index =
              "Three"
          }

in  let BindingBody
        : ADT
        = { cases =
              [ { args =
                    [ < Const =
                          { name = "s", type = "String" }
                      | Param :
                          Param
                      >
                    , param "false"
                    , param "true"
                    ]
                , name =
                    "BindingBody"
                }
              ]
          , type =
              "BindingBody"
          , index =
              "Boolean"
          }

in  let Test
        : ADT
        = { cases =
              [ { args =
                    [ < Const =
                          { name = "s", type = "String" }
                      | Param :
                          Param
                      >
                    , param "Nothing"
                    , < Const =
                          { name = "t", type = "String" }
                      | Param :
                          Param
                      >
                    , < Param =
                          { functor =
                              < F = { type = "Pair" } | I : {} >
                          , index =
                              "Just"
                          }
                      | Const :
                          Const
                      >
                    ]
                , name =
                    "TestOne"
                }
              , { args = [] : List ADT_arg, name = "TestTwo" }
              ]
          , type =
              "Test"
          , index =
              "Maybe Boolean"
          }

in  let NonEmpty
        : ADT
        = { cases =
              [ { name =
                    "NonEmpty"
                , args =
                    [ param "Nothing"
                    , < Param =
                          { functor =
                              < F = { type = "f" } | I : {} >
                          , index =
                              "Just"
                          }
                      | Const :
                          Const
                      >
                    ]
                }
              ]
          , type =
              "NonEmpty f"
          , index =
              "(Maybe i)"
          }

in  instantiate_all [ Pair, Triplet, TextLitF, MergeF, LetF, BindingBody ]
