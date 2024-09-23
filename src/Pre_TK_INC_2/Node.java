package Pre_TK_INC_2;


import java.util.ArrayList;
import java.util.List;

public class Node {
    /** An item stored in this node*/
    int item;
    /** The list of child node */
    List<Node> childs = new ArrayList<Node>(3);
    /** A utility value stored in that node */
    long utility = -1;

    /** The node constructor
     * @param item an item
     */
    public Node(int item) {
        this.item = item;
    }

    /**
     * Alternative constructor
     * @param item the item to store in that node
     * @param utility the utility to store in that node
     */
    public Node(int item, long utility) {
        this.item = item;
        this.utility = utility;
    }
}
