package graph;
import java.util.ArrayList;

public class Main{
    public static void main(String[] args) {
        ArrayList<Node> nodeList = new ArrayList<Node>();
        Node n0 = new Node(0);
        Node n1 = new Node(1);
        Node n2 = new Node(2);
        n0.neighbors.add(n1);
        n0.neighbors.add(n2);
        n1.neighbors.add(n2);
        n2.neighbors.add(n1);
        nodeList.add(n0);
        nodeList.add(n1);
        nodeList.add(n2);
        Graph g = new Graph(nodeList);

        System.out.println(g);
        
        g.tarjanSCC();
        System.out.println(g.SCCs);
    }
}