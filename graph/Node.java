package graph;

import java.util.ArrayList;

public class Node {
    public int index;
    public int num;
    public int lowlink;
    public boolean visited = false;
    public ArrayList<Node> neighbors = new ArrayList<Node>();
    public Node(int index){
        this.index = index;
    }
    public Node(int index, ArrayList<Node> neighbors){
        this.index = index;
        this.neighbors = neighbors;
    }

    public String toString(){
        return String.valueOf(this.index);
    }

}
