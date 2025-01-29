include "mexpr/externals.mc"

include "../../parser.mc"
include "../dists.mc"

-- need to have a dist environment
-- ANF for pruning --
lang MExprPPLPruningCPS = MExprPPL + DPPLParser + MExprCPS
  -- specialized normalize for assume and observe, cancel observe and prunes
  
  sem exprCps env k =
  | TmLet ({ body = TmCancel _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
  | TmLet ({ body = TmPrune _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
  | TmLet ({ body = TmPruned _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
 end

 lang TransformPruningDist = TransformDist + MExprPPL +DPPLParser

  -- a parameter of a pruned distribution can be either
  syn EnvParam =
  | PruneFParam () -- a distribution, e.g  Categorical (PruneFParam p1)
  | SeqFParam () -- a sequence, e.g. Categorical (SeqFParam [0.3,0.7])

  -- value of a pruned observe can be an IntValue or PrunedValue
  syn EnvValue =
  | PrunedValue () -- observe (PrunedValue (getSeq d_seq)) ..
  | IntValue ()  -- observe (IntValue 0) ..

  sem createEnvParam: Map Name EnvParam -> Expr -> Map Name EnvParam
  sem createEnvParam pruneEnv =
  | TmLet ({body = TmPruned p} & t) ->
    let env = mapInsert t.ident (PruneFParam ()) pruneEnv in
    createEnvParam (createEnvParam env t.body) t.inexpr
  | TmLet ({body=TmApp {lhs=TmVar v1, rhs=TmVar v2}}&t) ->
    match mapLookup v2.ident pruneEnv with Some (PruneFParam _) then
    let env = mapInsert t.ident (PruneFParam ()) pruneEnv in
      createEnvParam env t.inexpr
    else
      match mapLookup v1.ident pruneEnv with Some (PruneFParam _) then
      let env = mapInsert t.ident (PruneFParam ()) pruneEnv in
      createEnvParam env t.inexpr
    else
      createEnvParam pruneEnv t.inexpr
  | t -> sfold_Expr_Expr createEnvParam pruneEnv t

  sem createEnvDist: Map Name Expr -> Expr -> Map Name Expr
  sem createEnvDist distEnv =
  | TmLet ({body=TmDist ({dist=DCategorical _}&d)}&t) -> 
    createEnvDist (mapInsert t.ident t.body distEnv) t.inexpr
  | t -> sfold_Expr_Expr createEnvDist distEnv t


  sem createEnvValue: Map Name EnvValue -> Expr -> Map Name EnvValue
  sem createEnvValue env =
  | TmLet t -> let env = match tyTm (t.body) with TyInt _ then
          mapInsert t.ident (IntValue ()) env else
        match tyTm (t.body) with TyPruneInt _ then
          mapInsert t.ident (PrunedValue ()) env else
        env in
        createEnvValue (createEnvValue env t.body) t.inexpr
  | t -> sfold_Expr_Expr createEnvValue env t

  sem extractParam env =
  | TmVar ({ident=id}&v) ->
    match mapLookup id env.distEnv with Some (TmDist ({dist=DCategorical ({p=p}&d)}&t)) in
    match assignCons env.env p with Some x then x else (conapp_ "PruneGraph_SeqFParam" p)

  sem assignValueCons: (Map Name EnvValue) -> Expr -> Option Expr
  sem assignValueCons env =
  | TmVar v ->
    let varType = mapLookup v.ident env in
    match varType with Some varType then
      Some (assignValueConsH (TmVar v) varType)
    else None ()
  | t -> error "not in ANF-form"

  sem assignValueConsH t =
  | PrunedValue _ -> (conapp_ "PruneGraph_PrunedValue" t)
  | IntValue _ -> (conapp_ "PruneGraph_IntValue" t)

  -- assign the parameter construct for pruned distributions
  -- e.g. PCategorical (PruneFParam p1) where p1:PruneVar
  -- PCategorical (SeqFParam [0.25,0.25,0.25,0.25])
  sem assignCons: (Map Name EnvParam) -> Expr -> Option Expr
  sem assignCons env =
  | TmVar v ->
    let varType = mapLookup v.ident env in
    match varType with Some varType then
      Some (assignConsH (TmVar v) varType)
    else None ()
  | t -> error "not in ANF-form"

  sem assignConsH t =
  | PruneFParam _ -> (conapp_ "PruneGraph_PruneFParam" t)
  | SeqFParam _ -> (conapp_ "PruneGraph_SeqFParam" t)

end

lang DPPLPruningTransform = TransformPruningDist

  type Env = {
    prunedEnv:Map Name Expr,
    prunedFEnv:Map Name Expr,
    valueEnv:Map Name EnvValue,
    env:Map Name EnvParam,
    distEnv:Map Name Expr
  }

  --TODO: this needs a better way
  sem clearDists prunedFEnv =
  | TmDist ({dist=DCategorical {p=TmVar p}}&t)-> 
    match mapLookup p.ident prunedFEnv with Some _ then unit_
    else TmDist t
  | t -> smap_Expr_Expr (clearDists prunedFEnv) t
  
  sem replacePruneTypes =
  | t ->
    let t = smap_Expr_Type toRuntimePruneTyVar t in
    let t = smap_Expr_TypeLabel toRuntimePruneTyVar t in
    let t = smap_Expr_Pat replacePruneTyVarPat t in
    let t = smap_Expr_Expr replacePruneTypes t in
    withType (toRuntimePruneTyVar (tyTm t)) t

  sem toRuntimePruneTyVar : Type -> Type
  sem toRuntimePruneTyVar =
  | TyPruneInt t -> (tycon_ "PruneGraph_PruneVar")
  | ty -> smap_Type_Type toRuntimePruneTyVar ty

  sem replacePruneTyVarPat : Pat -> Pat
  sem replacePruneTyVarPat =
  | p ->
    let p = smap_Pat_Pat replacePruneTyVarPat p in
    withTypePat (toRuntimePruneTyVar (tyPat p)) p


  sem checkValidPrune env =
  | TmPrune p ->
    match p.dist with TmVar v in
    match mapLookup v.ident env.distEnv with Some (TmDist {dist=DCategorical {p=p}}) in
    match p with TmVar v in
    match mapLookup v.ident env.prunedFEnv with Some _ then
      error "Distribution of a pruned variable cannot have a pruned parameter"
    else p

sem createEnvs env =
  | TmLet ({body=TmPruned p} &t) ->
    let prunedEnv = mapInsert t.ident p.prune env.prunedEnv in
    (createEnvs {env with prunedEnv=prunedEnv} t.inexpr)
  | TmLet ({body=TmApp ({lhs=TmVar v1, rhs=TmVar v2}&a)} & t) ->
    match mapLookup v2.ident env.prunedFEnv with Some _ then
      error "Pruned variable shouldn't be applied as an argument anywhere than to a distribution"
    else match mapLookup v1.ident env.prunedFEnv with Some body then
      match mapLookup v2.ident env.prunedEnv with Some prune then 
        error "Cannot handle two pruned variable at the same time"
      else
        match body with TmApp ({lhs=TmApp ({lhs=_, rhs=TmLam l}&a2), rhs=_}&a1) in
        let lamBody = TmApp {{a with lhs=l.body} with rhs=TmVar v2} in
        let tbody = match inspectType (tyTm (t.body)) with TyArrow _ then
          nulam_ l.ident lamBody
        else TmApp {a1 with lhs=TmApp {a2 with rhs=nulam_ l.ident lamBody}} in
        let tbodye=TmApp {a1 with lhs=TmApp {a2 with rhs=nulam_ l.ident lamBody}} in
        let prunedFEnv = mapInsert t.ident tbodye env.prunedFEnv in
        (createEnvs {env with prunedFEnv=prunedFEnv} t.inexpr)
    else
    match mapLookup v2.ident env.prunedEnv with Some prune then
        let lamId = nameSym "" in
        let lamBody = TmApp {a with rhs=nvar_ lamId} in
        let tbody = match inspectType (tyTm (t.body)) with TyArrow _ then
          (nulam_ lamId lamBody)
        else appf2_ (var_ "initializePruneFVar") (nulam_ lamId lamBody) prune in
        let tbodyd = appf2_ (var_ "initializePruneFVar") (nulam_ lamId lamBody) prune in
        let prunedFEnv = mapInsert t.ident tbodyd env.prunedFEnv in
        (createEnvs {env with prunedFEnv=prunedFEnv} t.inexpr)
    else
      sfold_Expr_Expr createEnvs env (TmLet t)
  | t -> sfold_Expr_Expr createEnvs env t

  sem replaceTmPrunes env =
  | TmLet ({body=TmPrune p} &t) ->
    let param = checkValidPrune env (TmPrune p) in
    TmLet {{t with body=appf1_ (var_ "initializePruneRVar") param} with inexpr = replaceTmPrunes env t.inexpr}
  | TmLet ({body=TmPruned p} &t) ->
    let prunedEnv = mapInsert t.ident p.prune env.prunedEnv in
    (replaceTmPrunes {env with prunedEnv=prunedEnv} t.inexpr)
  | TmLet ({body=TmApp ({lhs=TmVar v1, rhs=TmVar v2}&a)} & t) ->
    match mapLookup v2.ident env.prunedFEnv with Some _ then
      error "Pruned variable shouldn't be applied as an argument anywhere than to a distribution"
    else match mapLookup v1.ident env.prunedFEnv with Some body then
      match mapLookup v2.ident env.prunedEnv with Some prune then 
        error "Cannot handle two pruned variable at the same time"
      else
        match body with TmApp ({lhs=TmApp ({lhs=_, rhs=TmLam l}&a2), rhs=_}&a1) in
        let lamBody = TmApp {{a with lhs=l.body} with rhs=TmVar v2} in
        let tbody = match inspectType (tyTm (t.body)) with TyArrow _ then
          nulam_ l.ident lamBody
        else TmApp {a1 with lhs=TmApp {a2 with rhs=nulam_ l.ident lamBody}} in
        let tbodye=TmApp {a1 with lhs=TmApp {a2 with rhs=nulam_ l.ident lamBody}} in
        let prunedFEnv = mapInsert t.ident tbodye env.prunedFEnv in
        TmLet {{t with body = tbody} with inexpr=(replaceTmPrunes {env with prunedFEnv=prunedFEnv} t.inexpr)}
    else
    match mapLookup v2.ident env.prunedEnv with Some prune then
        let lamId = nameSym "" in
        let lamBody = TmApp {a with rhs=nvar_ lamId} in
        let tbody = match inspectType (tyTm (t.body)) with TyArrow _ then
          (nulam_ lamId lamBody)
        else appf2_ (var_ "initializePruneFVar") (nulam_ lamId lamBody) prune in
        let tbodyd = appf2_ (var_ "initializePruneFVar") (nulam_ lamId lamBody) prune in
        let prunedFEnv = mapInsert t.ident tbodyd env.prunedFEnv in
        TmLet {{t with body = tbody} with inexpr=(replaceTmPrunes {env with prunedFEnv=prunedFEnv} t.inexpr)}
    else
      smap_Expr_Expr (replaceTmPrunes env) (TmLet t)
  | TmLet ({body=TmAssume t} &tl) ->
    if not (prunedObserve env (TmAssume t)) then TmLet {tl with inexpr = replaceTmPrunes env tl.inexpr} else
      error "assume cannot take a pruned random variable"
  | TmLet ({body=(TmObserve {value=TmVar v,dist=dist} | TmCancel {value=TmVar v,dist=dist}) & t } &tl) ->
    if not (prunedObserve env t) then TmLet tl else
      let value = match mapLookup v.ident env.prunedEnv with Some prune then prune else TmVar v in
      let value = match assignValueCons env.valueEnv value with Some x then x else error "wrong type at observe value field" in
      let param = extractParam env dist in
      let wId = nameSym "w" in
      let w = match t with TmObserve _ then
        nulet_ wId (appf3_ (var_ "observePrune") false_ value param) 
      else nulet_ wId (appf3_ (var_ "observePrune") true_ value param) in
      TmLet {{tl with body = bind_ w (ulet_ "" (weight_ (nvar_ wId)))} with inexpr=(replaceTmPrunes env tl.inexpr)}
  | t -> smap_Expr_Expr (replaceTmPrunes env) t

  sem prunedObserve env =
  | (TmObserve {value=TmVar v,dist=TmVar v2} | TmCancel {value=TmVar v,dist=TmVar v2}) & t  ->
      match mapLookup v2.ident env.distEnv with Some (TmDist {dist=DCategorical d}) then
        match mapLookup v.ident env.prunedEnv with Some _ then true else
        match d.p with TmVar v2 in
        match mapLookup v2.ident env.prunedFEnv with Some _ then true else false
      else false
  | TmAssume {dist=TmVar v2}  ->
      match mapLookup v2.ident env.distEnv with Some (TmDist {dist=DCategorical d}) then
        match d.p with TmVar v2 in
        match mapLookup v2.ident env.prunedFEnv with Some _ then true else false
      else false
  | _ -> false

  sem checkPrunes =
  | TmPrune _ -> error "should have been removed"
  | TmPruned _ -> error "should have been removed"
  | t -> smap_Expr_Expr checkPrunes t


 end

lang DPPLPruning = DPPLPruningTransform + MExprPPLPruningCPS
  sem prune =
  | prog -> 
    -- 2 -- get the types for distribution parameters
    -- type environment for distributions
    let env = createEnvParam (mapEmpty nameCmp) prog in
    let distEnv = createEnvDist (mapEmpty nameCmp) prog in
    let valueEnv = createEnvValue (mapEmpty nameCmp) prog in
    -- 4 -- whenever you encounter with a TmPrune change it to runtime variable PruneRVar
    -- 5 -- whenever you encounter with a TmPruned change it to runtime variable PruneFVar with a map in values
    match createEnvs {prunedFEnv=(mapEmpty nameCmp), prunedEnv=(mapEmpty nameCmp)} prog with ({prunedFEnv=prunedFEnv,prunedEnv=_}) in
    let prog = replaceTmPrunes {prunedEnv=(mapEmpty nameCmp),prunedFEnv=(mapEmpty nameCmp),valueEnv=valueEnv,env=env,distEnv=distEnv} prog in
    let prog = clearDists prunedFEnv prog in
    -- for debugging --
    checkPrunes prog;
    let prog = use DPPLPruningTransform in replacePruneTypes prog in
    prog
end
