package graph;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Stack;

public class Graph{
    private ArrayList<Node> adjency = new ArrayList<Node>();
    public ArrayList<ArrayList<Node>> SCCs = new ArrayList<ArrayList<Node>>();
    private ArrayList<Node> SCC = new ArrayList<Node>();
    private Stack<Node> stack = new Stack<Node>();
    private int num = 0;
    public Graph(ArrayList<Node> adjency){
        this.adjency = adjency;
    }

    public String toString(){
        String out = "";
        for(Node n : this.adjency){
            out += n.toString() + " : " + String.valueOf(n.neighbors) + "\n";
        }
        return out;
    }
   
    private void SCC(Node v){
        v.visited = true;
        v.num = this.num;
        v.lowlink = this.num;
        this.num++;
        this.stack.push(v);
        for(Node w : v.neighbors){
            if(!w.visited){
                this.SCC(w);
                v.lowlink = Math.min(v.lowlink, w.lowlink);
            } else if(this.stack.contains(w)){
                v.lowlink = Math.min(v.lowlink, w.num);
            }
        }
        if(v.lowlink==v.num){
            Node w;
            do{
                w = this.stack.pop();
                this.SCC.add(w);
            } while(w.index!=v.index);
            this.SCCs.add(new ArrayList<Node>(this.SCC));
            this.SCC.clear();
        }
    }
   
    public void tarjanSCC(){
        for(Node u : this.adjency){
            if(!u.visited){
                this.SCC(u);
            }
        }
    }
}