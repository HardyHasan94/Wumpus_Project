//===============================================================
/*
 * Artificial Intelligence: Wumpus Project
 * Full Observability Part
 * Author: Hardy Hasan
 */
//===============================================================

package fullObservability;
import wumpus.Agent;
import wumpus.World;
import java.util.*;


public class SearchAI extends Agent {
    private ListIterator<Action> planIterator;


//===============================================================
    /*
     * class Node:
     * constructs a node which contains i formation about the agent such as
     * state, parent state, action, pathCost, direction and whether it has an arrow
     */
//===============================================================
    public class Node implements Comparable<Node>{
        private final int[] state;
        private final Node parent;
        private final Action action;
        private final double pathCost;
        private final int agentDir;
        private final boolean hasArrow;

        public Node(int[] state, Node parent, Action action, double pathCost, int agentDir, boolean hasArrow){
            this.state = state;
            this.parent = parent;
            this.action = action;
            this.pathCost = pathCost;
            this.agentDir = agentDir;
            this.hasArrow = hasArrow;
        }
        public int[] getState(){
            return this.state;
        }
        public Node getParent(){
            return this.parent;
        }
        public Action getAction(){
            return this.action;
        }
        public double getPathCost(){
            return this.pathCost;
        }
        public int getAgentDir(){
            return this.agentDir;
        }
        public boolean hasArrow(){
            return this.hasArrow;
        }
        public boolean isRootNode(){
            return this.parent == null;
        }

        @Override
        public boolean equals(Object obj) {
            // Overriding equals method of Object:
            // two nodes are equal logically if their 'state', 'agentDir' and 'hasArrow' are equal

            if ((obj == null) || (getClass() != obj.getClass()))
                return false;

            final Node other = (Node) obj;  // typecast 'obj' to a Node

            if (state == null) {
                if (other.state != null)
                    return false;
            } else if (!Arrays.equals(state, other.state) || this.agentDir != other.getAgentDir() ||
                    this.hasArrow != other.hasArrow())
                return false;
            return true;
        }
        @Override
        public int hashCode(){
            // overriding hashCode of Node object:
            // the hashCode is now a combination of the hashCode of the 'state', 'agentDir' and
            // 'hasArrow' instance variable

            int result = 1;
            int hasArrowInt = hasArrow ? 1 : 0;
            final int prime = 71;
            result = result*prime + ((state == null) ? 0 : Arrays.hashCode(state)) + agentDir + 23*hasArrowInt;

            return result;
        }
        @Override
        public int compareTo(Node n){
            // comparison between nodes based on their pathCost
            if(this.pathCost > n.pathCost){
                return 1;
            }
            return -1;
        }
        @Override
        public String toString(){
            // a string representation of a Node for debugging purposes
            return "[Node:" + " state=" + Arrays.toString(state) + ", action=" + action + ", pathCost=" + pathCost +
                    ", agentDir=" + agentDir + "]";
        }
    }

//===============================================================
    /*
     * Helper functions:
     */
//===============================================================
    /**
     * Function that finds and returns the location of the gold
     * @param board: the game board
     * @return array containing gold location
     */
    public int[] goldLoc(World.Tile[][] board){
        // function that takes a tile board as input and returns the location of the gold
        int numCols = board.length;
        int numRows = board[0].length;

        for(int r = 0; r < numRows; r++){
            for(int c = 0; c < numCols; c++){
                if(board[c][r].getGold()){
                    return new int[]{c, r};
                }
            }
        }
        return new int[]{-1, -1}; // dummy return
    }

    /**
     * Function that creates a plan from current node to a goal node
     * @param goalNode Goal node
     * @param plan an empty LinkedList
     * @param offline: indicate whether in searching offline or not
     * @return plan sequence of actions that leads to the goal
     */
    public LinkedList<Action> createPlan(Node goalNode, LinkedList<Action> plan, boolean offline){
        LinkedList<Action> helper = new LinkedList<Action>();
        while(!goalNode.isRootNode()){
            helper.add(goalNode.getAction());
            goalNode = goalNode.getParent();
        }
        for(int i = helper.size() - 1; i >= 0; i--){
            plan.add(helper.get(i));
        }
        // if online search, then the current plan leads to desired destination
        if(!offline){return plan;}

        plan.add(Action.GRAB);
        plan.add(Action.TURN_LEFT);
        plan.add(Action.TURN_LEFT);
        for(int i = 0; i < helper.size(); i++){
            Action act = helper.get(i);
            if(act == Action.TURN_LEFT) {
                act = Action.TURN_RIGHT;
            }
            else if(act == Action.TURN_RIGHT){
                act = Action.TURN_LEFT;
            }
            else if(act == Action.SHOOT){
                act = Action.SHOOT;
            }
            if(i == helper.size()-1 && (act == Action.TURN_LEFT || act == Action.TURN_RIGHT)){
                ;
            }
            else{plan.add(act);}
        }
        for(int i = plan.size()-1; i >= 0; --i){
            if(plan.get(i) == Action.SHOOT){
                plan.remove(i);
                break;
            }
        }
        plan.add(Action.CLIMB);
        return plan;
    }

    /**
     * Function that finds the euclidean distance between two nodes
     * @param current current tile
     * @param goldLoc location of gold
     * @return Euclidean distance between current node and gold node
     */
    public double heuristic(Node current, int[] goldLoc){
        int[] currentState = current.getState();
        double x = currentState[1] - goldLoc[1];
        double y = currentState[0] - goldLoc[0];
        return Math.sqrt(x*x + y*y);
    }


//===============================================================
    /*
     * creating the PTS:
     * functions such as availableActions(), stateTransition(), goalTest() and actionCost() are implemented
     */
//===============================================================
    /**
     * Function that finds all the available actions in the current state
     * @param current: current node
     * @param board: game board
     * @param offline: indicate whether in searching offline or not
     * @return actions the agent is allowed to perform
     */
    public LinkedList<Action> availableActions(Node current, World.Tile[][] board, boolean offline){
        LinkedList<Action> actions = new LinkedList<Action>();
        int numCols = board.length;
        int numRows = board[0].length;
        int col = current.getState()[0];
        int row = current.getState()[1];
        int agentDir = current.getAgentDir();
        boolean hasArrow = current.hasArrow();
        Action lastAction = current.getAction();

        // if current tile has gold, then grab is only action
        if (board[col][row].getGold()) {
            actions.add(Action.GRAB);
            return actions;
        }
        switch (agentDir){
            case 0:
                if(col != numCols-1) {
                    if (board[col + 1][row].getPit()) {
                        ;
                    }
                    else if (board[col + 1][row].getWumpus()) {
                        if(!hasArrow){
                            actions.add(Action.FORWARD);
                        }
                        else{
                            actions.add(Action.SHOOT);
                        }
                    }
                    else{actions.add(Action.FORWARD);}
                }
                if(row != 0){
                    actions.add(Action.TURN_RIGHT);
                }
                if(row != numRows-1){
                    actions.add(Action.TURN_LEFT);
                }
                break;
            case 1:
                if(row != 0){
                    if(board[col][row-1].getPit()){
                        ;
                    }
                    else if(board[col][row-1].getWumpus()){
                        if(!hasArrow){
                            actions.add(Action.FORWARD);
                        }
                        else{
                            actions.add(Action.SHOOT);
                        }
                    }
                    else{actions.add(Action.FORWARD);}
                }
                if(col != 0){
                    actions.add(Action.TURN_RIGHT);
                }
                if(col != numCols-1){
                    actions.add(Action.TURN_LEFT);
                }
                break;
            case 2:
                if(col != 0){
                    if(board[col-1][row].getPit()){
                        ;
                    }
                    else if(board[col-1][row].getWumpus()){
                        if(!hasArrow){
                            actions.add(Action.FORWARD);
                        }
                        else{
                            actions.add(Action.SHOOT);
                        }
                    }
                    else{actions.add(Action.FORWARD);}
                }
                if(row != 0){
                    actions.add(Action.TURN_LEFT);
                }
                if(row != numRows-1){
                    actions.add(Action.TURN_RIGHT);
                }
                break;
            case 3:
                if(row != numRows-1){
                    if(board[col][row+1].getPit()){
                        ;
                    }
                    else if(board[col][row+1].getWumpus()){
                        if(!hasArrow){
                            actions.add(Action.FORWARD);
                        }
                        else{
                            actions.add(Action.SHOOT);
                        }
                    }
                    else{actions.add(Action.FORWARD);}
                }
                if(col != 0){
                    actions.add(Action.TURN_LEFT);
                }
                if(col != numCols-1){
                    actions.add(Action.TURN_RIGHT);
                }
                break;
        }
        // if lastAction was right/left, then no need to do a left/right action,
        // because it returns the agent back to where it has been
        // however, if we are in the online search, then it is okay to do so
        if(offline) {
            if (lastAction == Action.TURN_RIGHT || lastAction == Action.TURN_LEFT) {
                if (actions.contains(Action.TURN_LEFT)) {
                    actions.remove(Action.TURN_LEFT);
                }
                if (actions.contains(Action.TURN_RIGHT)) {
                    actions.remove(Action.TURN_RIGHT);
                }
            }
        }
        return actions;
    }

    /**
     * Function that finds the resulting state after performing some action in current state
     * @param current: current node
     * @param board: game board
     * @param action: the performed action
     * @param goldLoc: location of gold
     * @return resulting state
     */
    public Node stateTransition(Node current, Action action, World.Tile[][] board, int[] goldLoc){
        int currentCol = current.getState()[0];
        int currentRow = current.getState()[1];
        int nextCol = 0;
        int nextRow = 0;
        int nextAgentDir = current.getAgentDir();
        boolean hasArrow = current.hasArrow();
        double pathCost = current.getPathCost() + actionCost(current, action, board) + heuristic(current, goldLoc);
        int agentDir = current.getAgentDir();

        switch (agentDir){
            case 0:
                switch (action) {
                    case GRAB -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                    }
                    case SHOOT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        hasArrow = false;
                    }
                    case TURN_LEFT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 3;
                    }
                    case TURN_RIGHT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 1;
                    }
                    case FORWARD -> {
                        nextCol = currentCol + 1;
                        nextRow = currentRow;
                    }
                }
                break;
            case 1:
                switch (action) {
                    case GRAB -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                    }
                    case SHOOT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        hasArrow = false;
                    }
                    case TURN_LEFT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 0;
                    }
                    case TURN_RIGHT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 2;
                    }
                    case FORWARD -> {
                        nextCol = currentCol;
                        nextRow = currentRow-1;
                    }
                }
                break;
            case 2:
                switch (action) {
                    case GRAB -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                    }
                    case SHOOT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        hasArrow = false;
                    }
                    case TURN_LEFT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 1;
                    }
                    case TURN_RIGHT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 3;
                    }
                    case FORWARD -> {
                        nextCol = currentCol-1;
                        nextRow = currentRow;
                    }
                }
                break;
            case 3:
                switch (action) {
                    case GRAB -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                    }
                    case SHOOT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        hasArrow = false;
                    }
                    case TURN_LEFT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 2;
                    }
                    case TURN_RIGHT -> {
                        nextCol = currentCol;
                        nextRow = currentRow;
                        nextAgentDir = 0;
                    }
                    case FORWARD -> {
                        nextCol = currentCol;
                        nextRow = currentRow+1;
                    }
                }
                break;
        }
        int[] nextState = {nextCol, nextRow};
        return new Node(nextState, current, action, pathCost, nextAgentDir, hasArrow);
    }

    /**
     * Function that does the goal test, i.e. whether current tile is the goal tile
     * @param current: current node
     * @param dest: goal node
     * @return true/false
     */
    public boolean goalTest(Node current, int[] dest){
        int col = current.getState()[0];
        int row = current.getState()[1];
        return (col == dest[0] && row == dest[1]);

    }

    /**
     * Function that computes the cost of an action in the current tile
     * @param current: current node
     * @param action: the action
     * @param board: game board
     * @return cost
     */
    public int actionCost(Node current, Action action, World.Tile[][] board){
        int cost = 0;
        switch (action){
            case FORWARD, TURN_LEFT, TURN_RIGHT, GRAB -> {
                cost = 1;
            }
            case SHOOT -> {
                if(current.hasArrow()){
                    cost = 11;
                }
                else{cost = 1;}
            }
        }
        return cost;
    }


//===============================================================
    /*
     * Main Algorithm:
     * A* Search
     */
//===============================================================

    /**
     * Function that implements A* search
     * @param board Tile board
     * @param current: current tile
     * @param dest: destination tile
     * @param hasArrow: whether the agent has an arrow
     * @param dir: the direction of the agent
     * @param offline: indicate whether in searching offline or not
     * @return sequence of actions of how to get from current to dest
    */
    public LinkedList<Action> aStarSearch(World.Tile[][] board, int[] current, int[] dest, boolean hasArrow,
                                          int dir, boolean offline) {
        LinkedList<Action> plan = new LinkedList<Action>(); // list for actions
        PriorityQueue<Node> frontier = new PriorityQueue<Node>(); // priority queue for the unexplored nodes
        Hashtable<Node, Double> frontierTable = new Hashtable<Node, Double>(); // dictionary to retrieve nodes easily
        HashSet<Node> explored = new HashSet<Node>(); // hashset for the explored nodes

        Node root = new Node(current, null, Action.CLIMB, 0, dir, hasArrow); // root node
        frontier.add(root); //initialize frontier
        frontierTable.put(root, root.getPathCost());

        while (frontier.size() > 0) {
            // poll first node
            Node toExplore = frontier.poll();
            // goalTest
            if (goalTest(toExplore, dest)) {
                plan = createPlan(toExplore, plan, offline);
                return plan;
            }
            // add node to explored
            explored.add(toExplore);
            LinkedList<Action> availableActions = availableActions(toExplore, board, offline);
            for(Action action: availableActions){
                Node child = stateTransition(toExplore, action, board, dest);
                // if child not in any of explored or frontier
                if(!frontier.contains(child) && !explored.contains(child)){
                    frontier.add(child);
                    frontierTable.put(child, child.getPathCost());
                }
                // else if child in frontier but better path is found
                else if(frontier.contains(child)){
                    double oldPathCost = frontierTable.get(child);
                    if(oldPathCost > child.getPathCost()){
                        frontier.add(child);
                        frontierTable.put(child, child.getPathCost());
                    }
                }
            }
        }
        // if frontier is empty, then failed to retrieve gold, so Climb out
        plan.add(Action.CLIMB);
        return plan;
    }
    public SearchAI(){

    }


//===============================================================
    /*
     * Class Constructor:
     */
//===============================================================
    public SearchAI(World.Tile[][] board) {

        /* The world is board[column][row] with initial position (bottom left) being board[0][0] */
        LinkedList<Action> plan = new LinkedList<Action>();

        // first check if gold is in pit, if so, then Climb out
        int[] goldLoc = goldLoc(board);

        if(board[goldLoc[0]][goldLoc[1]].getPit()){
            plan.add(Action.CLIMB);
        }
        else{
            int[] current = {0, 0};
            boolean offline = true;
            plan = aStarSearch(board, current, goldLoc, true, 0, offline);
        }

        // This must be the last instruction.
        //System.out.println("The plan: " + plan);
        planIterator = plan.listIterator();
    }

//===============================================================
    /*
     * function getAction:
     * this function is called by the 'main' program, which returns actions from the plan
     */
//===============================================================
    @Override
    public Agent.Action getAction(boolean stench, boolean breeze, boolean glitter, boolean bump, boolean scream) {
        return planIterator.next();
    }


//===============================================================
    /*
     * END
     */
//===============================================================
}