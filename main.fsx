#light
open Microsoft.FSharp.Control.CommonExtensions
open Microsoft.FSharp.Control
open Microsoft.FSharp.NativeInterop

open System.Linq
open System
open System.Drawing
open System.Drawing.Imaging
open System.Windows.Forms
open System.Collections.Generic

// 0. define some global parameters
// ========================================================
//
let territorySize          = 120
let hive                   = new Rectangle (50, 50, 5, 5)
let maxFoodPerSquare       = 500
let chanceFoodPerSquare    = 2

let antMaxFoodCarried      = 50
let antPheromoneDrop       = 150.0
let pheromoneStickyness    = 5.0
let maxPheromone           = 2500.0
let tickLength             = 40
let antAdventurousness     = 10 // Lower is more adventurous

// 1. define some base functions and utilities
// ========================================================
//
module Event =
    let createEvent<'T>() =
        let ev = new Event<'T>()
        ev.Trigger, ev.Publish

// calculate the distance between 2 points
let hypot (w:float) (h:float) =
    Math.Sqrt (Math.Pow (Math.Abs w, 2.0) +
               Math.Pow (Math.Abs h, 2.0))

// add 2 2d points
let addxy (x1, y1) (x2, y2) =
    x1 + x2, y1 + y2

let random = new System.Random()

let alphaBlend (bg:Color) (src:Color) =
    let rat = 2uy

    let a = bg.A / rat + src.A / rat
    let r = bg.R / rat + src.R / rat
    let g = bg.G / rat + src.G / rat
    let b = bg.B / rat + src.B / rat

    Color.FromArgb ((int a), (int r), (int g), (int b))

// 2. define some core datastructures for the colony
// ========================================================
//
module AntColony =
    /// represents a single node in the ants territory
    type TerritoryNode =
        { food: int;
          pheromone: float;
          isHome: bool
          hasAnt: bool }
      with
        /// creates a new node with the default values
        static member newNode home =
            { food = 0;
              pheromone = 0.0;
              isHome = home;
              hasAnt = home }

        /// creates a new node with food
        static member newNodeFood f home =
            { food = f;
              pheromone = 0.0;
              isHome = home;
              hasAnt = home; }

        /// test if the node has food
        member n.hasFood = n.food > 0

        /// update where the pheromone value
        member n.updatePheromone food =
            if food then
              { n with pheromone = min maxPheromone (n.pheromone + antPheromoneDrop) }
            else
              { n with pheromone = max 0.0 (n.pheromone - pheromoneStickyness) }

        /// an ant arrives in the node
        member n.antArrive () =
            { n with hasAnt = true }

        /// an ant leaves the node
        member n.antLeave () =
            { n with hasAnt = false }

    /// represents an ant that moves within the territory
    type Ant =
        { foodCarried: int
          loc:         (int * int)
          locPrev:     (int * int)
          home:        (int * int) }
      with
        /// creates an new instance of an ant with the default values
        static member newAnt loc =
            { loc = loc; locPrev = loc; foodCarried = 0; home = loc; }

    /// the direction that the ants travel in
    type Direction =
        North | East | South | West | NorthEast | SouthEast | SouthWest | NorthWest

    /// 2d (x,y) delta for a given direction
    let deltaFromDirection d =
        match d with
        | North ->      0, -1
        | South ->      0,  1
        | West ->      -1,  0
        | East ->       1,  0
        | NorthEast ->  1, -1
        | SouthWest -> -1,  1
        | SouthEast ->  1,  1
        | NorthWest -> -1, -1

    /// The environment - represents both the ants and the nodes they move within
    type Env =
        { ants: seq<Ant>;
          territory: Map<int*int, TerritoryNode> }
      with
        /// initalize the environment with the default values
        static member initalize() =
            // create a list of points to represent the grid
            let points =
                seq { for i in [0 .. territorySize - 1] do
                        for j in [0 .. territorySize - 1] do
                            yield i,j }

            // a random point in the environment where food
            // is centered around
            let foodFocX, foodFocY =
                random.Next(0, territorySize - 1),
                random.Next(0, territorySize - 1)

            // randomly creat a node
            let createNode i j =
                let distFromFocal =
                    Math.Pow(hypot (float (i-foodFocX)) (float (j-foodFocY)), 1.5)

                let randomFoodDropValue =
                    random.Next( 0, chanceFoodPerSquare + Convert.ToInt32 distFromFocal)

                let home = hive.Contains(i, j)

                if randomFoodDropValue = 0 then
                    TerritoryNode.newNodeFood (random.Next( 0, maxFoodPerSquare )) home
                else
                    TerritoryNode.newNode home

            // create a map of points to node values
            let teritory = Seq.fold (fun acc (i,j) ->
                Map.add (i,j) (createNode i j) acc) Map.empty points

            // create the list of ants
            let antList =
                seq { for i in [hive.X .. hive.Right - 1] do
                            for j in [hive.Y .. hive.Bottom - 1] do
                                yield Ant.newAnt (i,j) }

            // return the environment
            { ants = antList;
                territory = teritory }

        /// replaces a node in the teritory with a new one
        member x.replaceNode loc newNode =
            if x.territory.ContainsKey(loc) then
                let newTerr = x.territory.Remove(loc)
                { x with territory = newTerr.Add(loc, newNode) }
            else
                { x with territory = x.territory.Add(loc, newNode) }

        member x.isValid (posx, posy) =
            /// test that a node is within the grid
            0 <= posx && posx < territorySize &&
            0 <= posy && posy < territorySize

    /// make an ant drop food some food
    let TNDropFood node fMax =
        let newNode = { node with food = (Math.Min (maxFoodPerSquare, node.food + fMax)) }
        newNode, (newNode.food - node.food)

    /// takes some food from a node
    let TNGetFood (node:TerritoryNode) fMax =
        if node.hasFood then
            let newNode =
                match Math.Max (0, node.food - fMax) with
                | n when n > 0 -> {node with food = n; pheromone = node.pheromone + antPheromoneDrop}
                | n -> {node with food = n;}
            newNode, (node.food - newNode.food)
        else node, 0

    /// attempt to move ant to a new node and return false if we can't
    let antGoToNode (env:Env) ant loc =
        if env.isValid loc  then
            let node = env.territory.[loc]

            if not node.hasAnt && (ant.locPrev <> loc) then
                let oldNode = env.territory.[ant.loc]
                let env = env.replaceNode ant.loc  (oldNode.antLeave())
                let env = env.replaceNode (loc) (node.antArrive().updatePheromone(ant.foodCarried >= antMaxFoodCarried))

                true, env, { ant with loc = loc; locPrev = ant.loc; }
            else
                false, env, ant
        else
            false, env, ant

    /// send an ant off in a given direction, trying the opposite
    /// direction if we can't
    let antGoInDirection env ant d =
        let delta = deltaFromDirection d
        antGoToNode env ant (addxy ant.loc delta)

    let randomDirection () =
        match random.Next( 0, 8 ) with
        | 0 -> North
        | 1 -> East
        | 2 -> South
        | 3 -> West
        | 4 -> NorthEast
        | 5 -> SouthEast
        | 6 -> NorthWest
        | 7 -> SouthWest
        | _ -> North

    /// move an ant in a random direction
    let antMoveRandomly env ant =
        antGoInDirection env ant (randomDirection())

    /// move an ant randomly until an acceptable node is found
    let rec antMoveRandomlyUntilTrue env ant =
        match antMoveRandomly env ant with
        | false,e,a -> antMoveRandomlyUntilTrue e a
        | r -> r

    let foodAndPheromoneOf (env:Env) ant d =
        let loc =
            let delta = deltaFromDirection d
            addxy ant.loc delta

        if env.isValid loc then
            let cell = env.territory.[loc]
            cell.food, cell.pheromone

        else -1, -1.0

    /// make the ant hunt according to the pheromone surrounding it
    let antHuntByPheromone env ant =
        if random.Next( 0, antAdventurousness ) = 0 then
            antMoveRandomly env ant
        else
            let searchSpace =
                [|(foodAndPheromoneOf env ant North),     North
                  (foodAndPheromoneOf env ant South),     South
                  (foodAndPheromoneOf env ant East),      East
                  (foodAndPheromoneOf env ant West),      West
                  (foodAndPheromoneOf env ant SouthWest), SouthWest
                  (foodAndPheromoneOf env ant NorthWest), NorthWest
                  (foodAndPheromoneOf env ant SouthEast), SouthEast
                  (foodAndPheromoneOf env ant NorthEast), NorthEast|]

            // find the maximum value in the search field
            let (pMax, dMax) = Array.max searchSpace

            let d =
                // make the presence of food more inportant than pheromone
                match pMax with
                | food,phero when food > 0 -> dMax
                | food,phero ->
                    // find all equal value of pheromone in the search field
                    let same = array.FindAll (searchSpace, fun (p,d) -> p >= pMax)
                    // choose, from cells that have this amount of pheromone,
                    // a random direction
                    let (_,d) = same.[random.Next(0, same.Length)]
                    d

            // attempt to go in the resulting direction.
            // if we can't, move randomly
            match antGoInDirection env ant (d) with
            | false, env, ant -> antMoveRandomly env ant
            | res -> res

    let antPathNext (pToX, pToY) (pFromX, pFromY) =
        let c = System.Collections.Generic.Comparer<int>.Default
        if pFromX = pToX && pFromY = pToY then
            pToX, pToY
        else
            pFromX + (c.Compare (pToX, pFromX)), pFromY + (c.Compare (pToY, pFromY))

    let findFirstNode pos env p =
        let rec loop pos =
            let node = env.territory.[pos]
            if p node then
                pos
            else
                let delta = deltaFromDirection ( randomDirection())
                loop (addxy pos delta)

        loop pos

    /// main encoding of ants behavior
    let behaveStep env ant =
        let curNode = env.territory.[ant.loc] in
        let b, env, ant =
            // do we need to drop some food
            if ant.foodCarried >= antMaxFoodCarried then
                // are we already home
                if ant.home = ant.loc then
                    let curNode, dropped = TNDropFood curNode ant.foodCarried
                    match dropped with
                    | n when n = ant.foodCarried ->
                        // all the food was dropped
                        true, (env.replaceNode ant.loc curNode), { ant with foodCarried = 0 }
                    | n ->
                        // only some of the food could be dropped.
                        // instead, make the colony larger, and drop in the new node
                        let nodeLoc = findFirstNode ant.loc env (fun c -> not c.isHome && c.food < maxFoodPerSquare)
                        let newEnv = env.replaceNode nodeLoc {env.territory.[nodeLoc] with isHome = true}

                        true, newEnv, {ant with home = nodeLoc }
                else
                    // find home
                    let homeX, homeY = ant.home
                    let loc = antPathNext (homeX, homeY) ant.loc

                    match antGoToNode env ant loc with
                    | false, e, a -> antMoveRandomly e a
                    | r -> r
            else
                if curNode.hasFood then
                    if curNode.isHome then
                        antMoveRandomly env ant
                    else
                        let tillMaxFood = antMaxFoodCarried - ant.foodCarried
                        let curNode,foodGot = (TNGetFood curNode tillMaxFood)

                        let currNode = env.replaceNode ant.loc curNode

                        if (foodGot > tillMaxFood) then
                            true, currNode, { ant with foodCarried = ant.foodCarried + foodGot; }
                        else
                            antMoveRandomly currNode {ant with foodCarried = ant.foodCarried + foodGot}
                else
                    antHuntByPheromone  env ant
        env, ant

// 3. define the application state machine for
//    computing the simulation.
// ========================================================
//
type msg = | Run | Exit | Pause | Step
/// A worker automaton is a reactive automaton running on a
/// dedicated thread of its own.
type Worker() =
    // Capture the synchronization context of the thread that creates this object. This
    // allows us to send messages back to the GUI thread painlessly.
    let callerCtxt =
        match System.Threading.SynchronizationContext.Current with
        | null -> null // System.ComponentModel.AsyncOperationManager.SynchronizationContext
        | x -> x

    let runInGuiCtxt f =
        match callerCtxt with
        | null ->
            if Application.OpenForms.Count > 0 then
                Application.OpenForms.Item(0).BeginInvoke(new MethodInvoker(fun _ -> f())) |> ignore
        | _ -> callerCtxt.Post((fun _ -> f()),null)

    let fireUpdates, onUpdates = Event.createEvent()

    let oneStep (env:AntColony.Env) =
        let env =
            let env, newAnts =
                env.ants |> Seq.fold (fun (env, acc) ant ->
                    let envNew, antNew = AntColony.behaveStep env ant
                    envNew, antNew :: acc ) (env, [])
            { env with ants = newAnts }

        runInGuiCtxt(fun _ -> fireUpdates([env]))
        env

    // The control logic is written using the 'async' non-blocking style.
    // We could also write this using a set of synchronous recursive functions,
    // or using a synchronous workflow, but it's more fun to use the
    // asynchronous version, partly because the MailboxProcessor
    // type gives us a free message queue.
    //
    // Wherever you see 'return!' in the code below you should interpret
    // that as 'go to the specified state'.
    let mailboxProcessor =
        MailboxProcessor.Start(fun inbox ->
            /// This is the States of the worker's automata using a set of
            /// tail-calling recursive functions.
            let rec Running(s) =
                async { let! msgOption = inbox.TryReceive(timeout=0)
                        match msgOption with
                        | None -> return! StepThen (SleepThen Running) s
                        | Some(msg) ->
                            match msg with
                            | Pause        -> return! Paused s
                            | Step         -> return! Running s
                            | Run          -> return! Running s
                            | Exit         -> return! Finish s }

            and StepThen f s =
                async { let s = oneStep(s)
                        return! f s }

            and SleepThen f s =
                async { // yield to give the GUI time to update
                        do! Async.Sleep(tickLength);
                        // Requeue in thread pool - strictly speaking we dont have to
                        // do this, but it ensures we reclaim stack on Mono and other
                        // platforms that do not take tailcalls on all architectures.
                        do! Async.SwitchToThreadPool()
                        return! f(s) }

            and Paused(s) =
                async { let! msg = inbox.Receive()
                        match msg with
                        | Pause          -> return! Paused s
                        | Step           -> return! StepThen Paused s
                        | Run            -> return! Running s
                        | Exit           -> return! Finish s }

            and Finish(s) =
                async { return () }

            // Enter the initial state
            Running (AntColony.Env.initalize()))

    /// public API to the worker
    member w.RunAsync () = mailboxProcessor.Post(Run)
    member w.StopAsync() = mailboxProcessor.Post(Pause)
    member w.ExitAsync() = mailboxProcessor.Post(Exit)
    member w.StepAsync() = mailboxProcessor.Post(Step)
    member w.Updates     = onUpdates

#nowarn "9"

/// Sets the three bytes following the given pointer to v
let private setPosition p (v:Color) =
    NativePtr.set p 0 v.B
    NativePtr.set p 1 v.G
    NativePtr.set p 2 v.R
    NativePtr.set p 3 v.A

let updateBitmap (bitmap:Bitmap) (pixels:seq<Color>) =
    let w, h = bitmap.Width, bitmap.Height

    // Get the bitmap data for a 32 bpp bitmap with a Read Write lock
    let bd = bitmap.LockBits(Rectangle(0, 0, w, h),
                ImageLockMode.ReadWrite,
                PixelFormat.Format32bppArgb)

    // Setup the pointer
    let origin = NativePtr.ofNativeInt bd.Scan0
    let (p:ref<nativeptr<byte>>) = ref origin

    pixels |> Seq.iteri  (fun i pix ->
        setPosition !p pix
        if i % territorySize - 1 = 0 && i > 0 then
            p := NativePtr.add origin (i / territorySize * 4)
        else
            p := NativePtr.add !p bd.Stride)

    // Unlock the image bytes
    bitmap.UnlockBits(bd)

// 4. run the application as a number of simulateous
//    colony simulations.
// ========================================================
//
let main() =
    let foodColor = Color.FromArgb 0xFF88A84E // green
    let pheromoneColor = Color.FromArgb 0xFF01605E // blue
    let antColor = Color.FromArgb 0xFFC3A6E0 // purple
    let homeColor = Color.FromArgb 0xAA645636 // brown
    let w = 480

    let form =
        new Form(
            Visible   = true,
            BackColor = Color.White,
            Text      = "Ant Colony",
            Width     = w * 2,
            Height    = w * 2)

    // 4x4 grid
    for x in [ 0 .. 1 ] do
        for y in [ 0 .. 1 ] do
            let worker = new Worker()

            let bitmap = new Bitmap(territorySize, territorySize, PixelFormat.Format32bppArgb)
            let pb = { new PictureBox(SizeMode=PictureBoxSizeMode.Zoom) with
                        override b.OnPaint e =
                            e.Graphics.InterpolationMode <- Drawing2D.InterpolationMode.NearestNeighbor
                            base.OnPaint e }

            pb.Size <- new Size(w, w)
            pb.Location <- new Point( x * w, y * w)
            pb.Image <- bitmap

            form.Controls.Add(pb)

            worker.Updates.Add(fun updates ->
                for (env:AntColony.Env) in updates do
                    let lst =
                        Map.toList env.territory
                        |> Seq.map (fun (_,node) ->
                            match node with
                            | node when node.isHome ->
                                match node with
                                | node when node.food > 0 ->
                                    let alpha = float node.food / float maxFoodPerSquare * 255.0
                                    alphaBlend homeColor (Color.FromArgb(Convert.ToInt32 alpha , foodColor))
                                |_ -> homeColor

                            | node when node.hasAnt ->
                                antColor

                            | node when node.food > 0 ->
                                let alpha = float node.food / float maxFoodPerSquare * 255.0
                                Color.FromArgb(Convert.ToInt32 alpha , foodColor)

                            | node when node.pheromone > 0.0 ->
                                let alpha = node.pheromone / maxPheromone * 255.0
                                Color.FromArgb(Convert.ToInt32 alpha , pheromoneColor)

                            |_ -> Color.White)

                    updateBitmap bitmap lst
                    pb.Invalidate())

    form.Activate()
    Application.Run(form)

[<STAThread>]
do main()