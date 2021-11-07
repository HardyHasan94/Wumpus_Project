//===============================================================
	/*
	 * Artificial Intelligence: Wumpus Project
	 * Partial Observability(Online) Part
	 * Author: Hardy Hasan
	 */
//===============================================================

package partialObservability;
import fullObservability.SearchAI;
import org.tweetyproject.logics.pl.reasoner.SatReasoner;
import org.tweetyproject.logics.pl.sat.*;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import wumpus.World;
import wumpus.Agent;
import org.tweetyproject.logics.pl.syntax.*;
import java.util.Arrays;
import java.util.LinkedList;


//===============================================================
	/*
	 * empty class constructor
	 */
//===============================================================
public class MyAI extends Agent {
	public MyAI() {
	}


//===============================================================
	/*
	 * some useful variables
	 */
//===============================================================
	int leftMostCol = 0;
	int rightMostCol = 3; // initially assuming 2x2 world, until finding the true dimensions
	int bottomMostRow = 0;
	int topMostRow = 3;
	boolean rightBorderNotFound = true; // if the true borders till not found
	boolean topBorderNotFound = true;
	int currentCol = 0;
	int currentRow = 0;
	int dir = 0; // direction of agent
	boolean hasArrow = true;
	boolean goldFound = false;
	boolean wumpusAlive = true;
	Action lastAction = Action.CLIMB; // when starting the game
	private World.Tile[][] board; // constructing world boards

//===============================================================
	/*
	 * Helper functions
	 */
//===============================================================
	/**
	 * a function that checks whether a linked list contains an array
	 * @param list: the list
	 * @param array: the array
	 * @return true/false
	 */
	public boolean contain(LinkedList<int[]> list, int[] array){
		for(int[] el: list){
			if(Arrays.equals(array, el)){
				return true;
			}
		}
		return false;
	}

	/**
	 * a function that removes all invalid tiles element from safe/unvisited tiles list.
	 * A tile is invalid if it's outside of the borders of the board
	 * @param safe: list of safe tiles
	 * @param unvisited: not yet visited tiles
	 * @param KB: the knowledge base
	 */
	public void removeInvalidTiles(LinkedList<int[]> safe, LinkedList<int[]> unvisited, PlBeliefSet KB) {
		if (dir == 0) {
			for (int row = 0; row < topMostRow; ++row) {
				int[] tile = {rightMostCol, row};
				KB.add(new Negation(constructPropArray("P", tile)));
				KB.add(new Negation(constructPropArray("W", tile)));
				if (contain(safe, tile)) {
					safe.removeIf(el -> Arrays.equals(el, tile));
				}
				if (contain(unvisited, tile)) {
					unvisited.removeIf(el -> Arrays.equals(el, tile));
				}
			}
		} else if (dir == 3) {
			for (int col = 0; col < rightMostCol; ++col) {
				int[] tile = {col, topMostRow};
				KB.add(new Negation(constructPropArray("P", tile)));
				KB.add(new Negation(constructPropArray("W", tile)));
				if (contain(safe, tile)) {
					safe.removeIf(el -> Arrays.equals(el, tile));
				}
				if (contain(unvisited, tile)) {
					unvisited.removeIf(el -> Arrays.equals(el, tile));
				}
			}
		}
	}

	/**
	 * function that change variable 'dir' based on the action performed and the current direction
	 */
	public void changeDir(Action action){
		switch (action){
			case TURN_LEFT:
				if(dir == 0){dir = 3;}
				else{--dir;}
				break;
			case TURN_RIGHT:
				if(dir == 3){dir = 0;}
				else{++dir;}
				break;
		}
	}

	/**
	 * function that returns the current believed dimension of the board
	 */
	public int[] currentDims() {
		if (rightBorderNotFound) {
			if (topBorderNotFound) {
				return new int[]{rightMostCol + 1, topMostRow + 1};
			} else {
				return new int[]{rightMostCol + 1, topMostRow};
			}
		} else {
			if (topBorderNotFound) {
				return new int[]{rightMostCol, topMostRow + 1};
			} else {
				return new int[]{rightMostCol, topMostRow};
			}
		}
	}

	/**
	 * functions that checks whether a column is outside of the board
	 * @param col: column
	 * @param dir: right or left side
	 * @return true/false
	 */
	public boolean colOutOfBorder(int col, String dir){
		boolean res = false;
		switch(dir){
			case "left":
				if(col-1 < leftMostCol){
					res = true;
				}
				break;
			case "right":
				if(rightBorderNotFound) {
					if (col + 1 > rightMostCol) {
						res = true;
					}
				}
				else{
					if (col + 1 >= rightMostCol) {
						res = true;
					}
				}
				break;
		}
		return res;
	}

	/**
	 * functions that checks whether a row is outside of the board
	 * @param row: column
	 * @param dir: up or down side
	 * @return true/false
	 */
	public boolean rowOutOfBorder(int row, String dir){
		boolean res = false;
		switch(dir){
			case "bottom":
				if(row-1 < bottomMostRow){
					res = true;
				}
				break;
			case "top":
				if(topBorderNotFound) {
					if (row + 1 > topMostRow) {
						res = true;
					}
				}
				else{
					if (row + 1 >= topMostRow) {
						res = true;
					}
				}
				break;
		}
		return res;
	}
	/**
	 * functions that create proposition from a string, column and row
	 * @param s: the string
	 * @param col: column
	 * @param row: row
	 * @return proposition of the form string_[col, row]
	 */
	public Proposition constructProp(String s, int col, int row){
		String p = s + "_[" + col + ", " + row + "]";
		return new Proposition(p);
	}

	/**
	 * functions that create proposition from a string and array
	 * @param s: the string
	 * @param arr: the array
	 * @return proposition of the form string_array
	 */
	public Proposition constructPropArray(String s, int[] arr){
		String p = s + "_" + Arrays.toString(arr);
		return new Proposition(p);
	}

	/**
	 * Function that returns the neighboring locations given a state location
	 * @param currentLoc location of current tile
	 * @return neighboring tile locations
	 */
	public LinkedList<int[]> neighbors(int[] currentLoc){
		int col = currentLoc[0];
		int row = currentLoc[1];
		LinkedList<int[]> neighbors = new LinkedList<>();

		if(!colOutOfBorder(col, "left")){
			int[] n =  {col-1, row};
			neighbors.add(n);
		}
		if(!colOutOfBorder(col, "right")){
			int[] n =  {col+1, row};
			neighbors.add(n);
		}
		if(!rowOutOfBorder(row, "bottom")){
			int[] n =  {col, row-1};
			neighbors.add(n);
		}
		if(!rowOutOfBorder(row, "top")){
			int[] n =  {col, row+1};
			neighbors.add(n);
		}

		return neighbors;
	}

	/**
	 * Function that finds and returns the euclidean distance between two tiles
	 * @param tile: a tile
	 * @param current: location of agent
	 * @return distance
	 */
	public double distance(int[] current, int[] tile){
		double x = current[0] - tile[0];
		double y = current[1] - tile[1];
		return Math.sqrt(x*x + y*y);
	}

	/**
	 * Function that finds and returns the closest tile to current tile among a list of tiles
	 * @param unvisited: list of tiles
	 * @param current: location of agent
	 * @return closest: the tile closest to current location
	 */
	public int[] closestTile(LinkedList<int[]> unvisited, int[] current){
		int[] closest = unvisited.get(0); // assume first tile is closest tile
		double minDist = distance(current, closest); // distance to current
		for(int[] tile: unvisited){
			double dist = distance(current, tile);
			if(dist < minDist){
				minDist = dist;
				closest = tile;
			}
		}
		unvisited.remove(closest);
		return closest;
	}


//===============================================================
	/*
	 * Other functions that:
	 * update/query the knowledge base
	 * uses percepts and notices effects of the performed action
	 * creates a hypothetical game board filled with the knowledge so far deduced from the KB
	 * find all safe tiles
	 * find tiles not known to be safe or dangerous
	 * find location or believed location of Wumpus
	 * update visited and finds non-visited tiles
	 */
//===============================================================

	/**
	 * Function that initializes a KB with known truths
	 * @param KB empty knowledge base
	 * @return KB filled with axioms
	 */
	public PlBeliefSet initKB(PlBeliefSet KB){
		SatSolver.setDefaultSolver(new Sat4jSolver());

		// initializing a KB for a 7x7 world
		int numCols = 8;
		int numRows = 8;

		// there is no pit or wumpus in [0, 0]
		Negation noPit = new Negation(constructProp("P", 0, 0));
		Negation noWumpus = new Negation(constructProp("W", 0, 0));
		KB.add(noPit, noWumpus);

		// there is exactly one wumpus:
		// first 1: the wumpus must be in one of the tiles
		Disjunction atLeastOneWumpus = new Disjunction();
		for(int col = 0; col < numCols; ++col){
			for(int row = 0; row < numRows; ++row){
				Proposition p = constructProp("W", col, row);
				atLeastOneWumpus.add(p);

				// part 2: there is at most one wumpus
				// for each pair of tiles, only one of them can contain the wumpus
				for(int i = row; i < numRows; ++i){
					for(int j = col+1; j < numCols; ++j) {
						Negation n1 = new Negation(constructProp("W", col, row));
						Negation n2 = new Negation(constructProp("W", j, i));
						Disjunction d = new Disjunction(n1, n2);
						KB.add(d);
					}
				}
			}
		}
		KB.add(atLeastOneWumpus);
		return KB;
	}

	/**
	 * Function that adds the equivalence of having pits in the neighbors if current tile is breezy
	 * @param KB knowledge base
	 */
	public void nextToPit(PlBeliefSet KB){
		int[] currentLoc = {currentCol, currentRow};
		// first, tell KB that no pit is in current
		KB.add(new Negation(constructPropArray("P", currentLoc)));

		LinkedList<int[]> neighbors = neighbors(currentLoc);
		Disjunction dP = new Disjunction();
		for(int[] nb: neighbors){
			if(!contain(safe, nb)) {
				dP.add(constructPropArray("P", nb));
			}
		}
		Proposition B = constructPropArray("B", currentLoc);
		Equivalence eP = new Equivalence(B, dP);
		KB.add(eP.toCnf());
	}

	/**
	 * Function that adds the equivalence of having wumpus in a neighbor if current tile is stenchy
	 * @param KB knowledge base
	 */
	public void nextToWumpus(PlBeliefSet KB){
		int[] currentLoc = {currentCol, currentRow};
		// first, tell KB that no wumpus is in current
		KB.add(new Negation(constructPropArray("W", currentLoc)));

		LinkedList<int[]> neighbors = neighbors(currentLoc);
		Disjunction dW = new Disjunction();
		for(int[] nb: neighbors){
			if(!contain(safe, nb)) {
				dW.add(constructPropArray("W", nb));
			}
		}
		Proposition S = constructPropArray("S", currentLoc);
		Equivalence eP = new Equivalence(S, dW);
		KB.add(eP.toCnf());
	}

	/**
	 * Function that takes perceptions and created propositions about the world
	 * @param percepts percepts
	 * @param KB knowledge base
	 * @param safe: safe tiles
	 * @param unvisited: unvisited tiles
	 */
	public void perceived(LinkedList<Boolean> percepts, PlBeliefSet KB, LinkedList<int[]> safe,
						  LinkedList<int[]> unvisited){
		boolean stench = percepts.get(0);
		boolean breeze = percepts.get(1);
		boolean glitter = percepts.get(2);
		boolean bump = percepts.get(3);
		boolean scream = percepts.get(4);

		// when finding gold
		if(glitter){
			goldFound = true;
		}
		// when hitting a wall, maybe world dimensions are found
		if(bump){
			if(rightBorderNotFound || topBorderNotFound) {
				if (dir == 0) {
					rightMostCol = currentCol+1;
					rightBorderNotFound = false;
					removeInvalidTiles(safe, unvisited, KB);
				} else if (dir == 3) {
					topMostRow = currentRow+1;
					topBorderNotFound = false;
					removeInvalidTiles(safe, unvisited, KB);
				}
			}
		}

		// for any tile, it is breezy/stenchy if some neighbor has pit/wumpus
		if(wumpusAlive) {
			nextToWumpus(KB);
		}
		nextToPit(KB);

		// if stench, then current tile has wumpus nearby, otherwise add no stench in current:
		if(stench){
			KB.add(constructProp("S", currentCol, currentRow));
		}
		else{KB.add(new Negation(constructProp("S", currentCol, currentRow)));}

		// if breeze, then there is a pit nearby, otherwise add no breeze in current:
		if(breeze){
			KB.add(constructProp("B", currentCol, currentRow));
		}
		else{KB.add(new Negation(constructProp("B", currentCol, currentRow)));}

		// if scream, then wumpus is martyred:
		if(scream){
			wumpusAlive = false;
		}
	}

	/**
	 * Function that updates variables after each action
	 * @param KB: the knowledge base
	 * @param action the taken action
	 * @param percepts: the percepts
	 */
	public void performedAction(PlBeliefSet KB, Action action, LinkedList<Boolean> percepts){
		boolean stench = percepts.get(0);
		boolean breeze = percepts.get(1);
		boolean glitter = percepts.get(2);
		boolean bump = percepts.get(3);
		boolean scream = percepts.get(4);

		switch (action){
			case CLIMB:
				// do nothing
				break;
			// if forward, then increase currentCol/currentRow depending on direction
			case FORWARD:
				if(!bump) {
					if(dir == 0){
						++currentCol;
						if(currentCol == rightMostCol){
							++rightMostCol;
						}
					}
					else if(dir == 1){--currentRow;}
					else if(dir == 2){--currentCol;}
					else{
						++currentRow;
						if(currentRow == topMostRow){
							++topMostRow;
						}
					}
				}
				break;
			case TURN_LEFT:
				changeDir(Action.TURN_LEFT);
				break;
			case TURN_RIGHT:
				changeDir(Action.TURN_RIGHT);
				break;
			case SHOOT:
				hasArrow = false;
		}
	}

	/**
	 * Function that finds and returns all the safe  neighboring tiles to current
	 * @param KB the knowledge base
	 * @param safe: list of safe tiles
	 * @return safe: a list of safe tiles
	 */
	public LinkedList<int[]> safeTiles(PlBeliefSet KB, LinkedList<int[]> safe){
		int lowCol = 0;
		int lowRow = 0;
		int upCol = currentCol+1;
		int upRow = currentRow+1;
		if(currentCol > 0){
			lowCol = currentCol-1;
		}
		if(currentCol == rightMostCol-1 && !rightBorderNotFound){
			upCol = currentCol;
		}
		if(currentRow > 0){
			lowRow = currentRow-1;
		}
		if(currentRow == topMostRow-1 && !topBorderNotFound){
			upRow = currentRow;
		}

		for(int col = lowCol; col <= upCol; ++col) {
			for (int row = lowRow; row <= upRow; ++row) {
				int[] nb = {col, row};
				if (!contain(safe, nb)) {
					Negation nW = new Negation(constructPropArray("W", nb));
					Negation nP = new Negation(constructPropArray("P", nb));

					// a tile is safe if it can be deduced that it doesn't contain a pit or wumpus
					if (reasoner.query(KB, nP)) {
						if (wumpusAlive) {
							if (reasoner.query(KB, nW)) {
								safe.add(nb);
							}
						}
						if(!wumpusAlive){
							safe.add(nb);
						}
					}
				}
			}
		}
		return safe;
	}

	/**
	 * Function that creates a board where all non-safe tiles contain a pit
	 * @param safe list of safe tiles
	 * @return board: the corresponding board
	 */
	public World.Tile[][] safeBoard(LinkedList<int[]> safe) {
		int[] dims = currentDims();
		int columns = dims[0];
		int rows = dims[1];
		board = new World.Tile[columns][rows];
		for(int col = 0; col < columns; ++col) {
			for (int row = 0; row < rows; ++row) {
					int[] t = {col, row};
					if (contain(safe, t)) {
						board[col][row] = new World.Tile();
					} else {
						board[col][row] = new World.Tile();
						board[col][row].setPit();
					}
				}
			}
		return board;
	}

	/**
	 * Function that creates a list of all safe and unvisited tiles
	 * @param visited list of visited tiles
	 * @param safe: list of safe tiles
	 * @return unvisited: the corresponding board
	 */
	public LinkedList<int[]> unvisitedTiles(LinkedList<int[]> visited,LinkedList<int[]> unvisited,
											LinkedList<int[]> safe){
		for(int[] a: safe){
			if(!contain(visited, a) && !contain(unvisited, a)){
				unvisited.add(a);
			}
		}
		return unvisited;
	}

	/**
	 * Function that looks for tiles that may have a wumpus. If there are more than one tile, it returns any of them
	 * @param KB: the knowledge base
	 * @param board: safeBoard needs to be changed so that the chosen tile has a wumpus
	 * @return wumpusLoc: the tile that contains/may contain the wumpus
	 */
	public int[] possibleWumpusLoc(PlBeliefSet KB, World.Tile[][] board){
		int[] dims = currentDims();
		int columns = dims[0];
		int rows = dims[1];
		// first looking for the real wumpus location
		for(int col = 0; col < columns; ++col) {
			for (int row = 0; row < rows; ++row) {
				int[] t = {col, row};
				if (!contain(safe, t)) {
					if (reasoner.query(KB, new Negation(constructProp("P", col, row)))) {
						if(reasoner.query(KB, constructProp("W", col, row))){
							board[col][row].setWumpus();
							board[col][row].unSetPit();
							return new int[]{col, row};
						}
					}
				}
			}
		}
		// if the real location is not found, then look for a tile that is not known to be wumpus-free
		for(int col = 0; col < columns; ++col) {
			for (int row = 0; row < rows; ++row) {
				// if a non-safe tile is not known to be wumpus-free, then it may have a wumpus
				int[] t = {col, row};
				if (!contain(safe, t)) {
					if (!reasoner.query(KB, new Negation(constructProp("W", col, row)))) {
						board[col][row].setWumpus();
						// if it is not known for sure that a pit is in the tile, then return it
						if (!reasoner.query(KB, (constructProp("P", col, row)))) {
							board[col][row].unSetPit();
							return new int[]{col, row};
						}
					}
				}
			}
		}
		return new int[]{-1, -1}; // otherwise return dummy tile, indicating mission impossible
	}

	/**
	 * Function that finds and returns a tile not known to be safe and not known to have a pit
	 * @param KB: the knowledge base
	 * @param safe: list of safe tiles so far found
	 * @return non-safe tile
	 */
	public LinkedList<int[]> nonSafeTile(PlBeliefSet KB, LinkedList<int[]> safe){
		int[] dims = currentDims();
		int columns = dims[0];
		int rows = dims[1];
		LinkedList<int[]> nonSafe = new LinkedList<>();
		for(int col = 0; col < columns; ++col) {
			for (int row = 0; row < rows; ++row) {
				int[] t = {col, row};
				// if t is not safe and does not contain a pit, then return it
				if (!contain(safe, t)) {
					if (!reasoner.query(KB, constructProp("P", col, row))) {
						// we have also to be sure that there is no wumpus
						if (!reasoner.query(KB, constructProp("W", col, row))) {
							nonSafe.add(t);
						}
					}
				}
			}
		}
		return nonSafe;
	}

//===============================================================
	/*
	 * necessary variables:
	 * KB: the knowledge base
	 * reasoner: a reasoner for reasoning tasks. Uses Sat4jSolver as SAT solver
	 * safe: list of safe tiles
	 * visited: tiles already visited
	 * unvisited: tiles yet to be visited
	 * plan: current plan
	 * mySearch: a SearchAI instance
	 */
//===============================================================
	// initializing the knowledge base and filling it with axioms
	PlBeliefSet KB = initKB(new PlBeliefSet());

	// creating a reasoner
	SatReasoner reasoner = new SatReasoner();

	// lists of safe, visited, unvisited and stenchy tiles
	LinkedList<int[]> safe = new LinkedList<>();
	LinkedList<int[]> visited = new LinkedList<>(); // visited tiles
	LinkedList<int[]> unvisited = new LinkedList<>(); // unvisited tiles

	// plan
	LinkedList<Action> plan = new LinkedList<>(); // planning a sequence of actions

	// a SearchAI object, in order to reach the methods of that class
	SearchAI mySearch = new SearchAI();


//===============================================================
	/*
	 * function getAction
	 * implement the Hybrid-Agent function
	 */
//===============================================================

	public Agent.Action getAction
	(
		boolean stench,
		boolean breeze,
		boolean glitter,
		boolean bump,
		boolean scream
	)
	{
		// what is perceived
		LinkedList<Boolean> percepts = new LinkedList<>(Arrays.asList(stench, breeze, glitter, bump, scream));

		// first thing, update variables after last performed action
		performedAction(KB, lastAction, percepts);

		// current tile
		int[] current = {currentCol, currentRow};

		// the search is done online
		boolean offline = false;

		// if agent is in a tile for first time or it bumped or heard scream, then process the precepts
		if(!contain(visited, current) || bump || scream) {
			perceived(percepts, KB, safe, unvisited);
			// if current tile not already in the safe list, then add it
			if(!contain(safe, current)) {
				safe.add(current);
			}
			// tiles known to be safe
			safe = safeTiles(KB, safe);
			// add current tile to visited ones
			visited.add(current);
		}

		// a board where only safe tiles are pit-free
		World.Tile[][] safeBoard = safeBoard(safe);

		// if gold is found, then continue to follow the plan or create a plan
		if(goldFound){
			if(plan.size() == 0){
				int[] dest = {0, 0};
				//make plan
				plan = mySearch.aStarSearch(board, current, dest, hasArrow, dir, offline);
				plan.add(0, Action.GRAB); // add grab as first action
				plan.add(Action.CLIMB); // climb out as last action
			}
		}

		// if plan is empty: make a plan to the closest unvisited tile
		 if(plan.size() == 0){
			unvisited = unvisitedTiles(visited, unvisited, safe);

			// if there are still tiles not visited, then go to the closest one
			if(unvisited.size() > 0) {
				int[] closest = closestTile(unvisited, current);
				plan = mySearch.aStarSearch(safeBoard, current, closest, hasArrow, dir, offline);
			}
		}

		// if plan is empty and hasArrow: choose one of possible wumpus tiles, plan a shooting
		if(plan.size() == 0 && hasArrow){
			int[] dest = possibleWumpusLoc(KB, safeBoard);
			// if 'dest' is not dummy, then make plan, otherwise there are wumpus and pit in this tile
			if(!Arrays.equals(dest, new int[]{-1, -1})) {
				plan = mySearch.aStarSearch(safeBoard, current, dest, hasArrow, dir, offline);
				if(plan.size() == 1 && plan.get(0) == Action.CLIMB){
					plan.poll();
				}
			}
		}

		// if plan still empty: take a risk by moving to a tile that's not known to be safe
		// however, if taking risks, then the performance decreases significantly
		// thus we can choose how often to take risks by introducing a random variable
		// riskTaking >= 1.0 means not taking any chances
		double riskTaking = Math.random();
		if(plan.size() == 0 && riskTaking >= 1.0) {
			LinkedList<int[]> nonSafes = nonSafeTile(KB, safe);
			while (nonSafes.size() > 0) {
				int[] dest = closestTile(nonSafes, current);
				safeBoard[dest[0]][dest[1]].unSetPit();
				plan = mySearch.aStarSearch(safeBoard, current, dest, hasArrow, dir, offline);
				safeBoard[dest[0]][dest[1]].setPit();
				if (!(plan.size() == 1 && plan.get(0) == Action.CLIMB)) {
					break;
				} else {
					plan.poll();
				}
			}
		}



		// if plan is empty: go back home
		if(plan.size() == 0){
			int[] dest = {0, 0};
			plan = mySearch.aStarSearch(safeBoard, current, dest, hasArrow, dir, offline);
			plan.add(Action.CLIMB);
		}

		// take an action
		if(plan.size() != 0) {
			Agent.Action action = plan.poll();
			lastAction = action;
			// return action
			return action;
		}
		return Action.FORWARD; // hopefully never get here
	}

//===============================================================
	/*
	 * END
	 */
//===============================================================
}