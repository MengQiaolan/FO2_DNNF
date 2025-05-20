from enum import Enum

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_agraph import graphviz_layout

class NodeType(Enum):
    AND = 'and'
    OR = 'or'
    LEAF = 'leaf'
    
    def __str__(self):
        return self.value

class Node:
    def __init__(self, type: NodeType, index: int, value = None, mark = None):
        self.type = type
        self.index = index
        self.mark = mark
        self.children: set[int] = set()
        self.parents: set[int] = set()
        self.literal_str = None
        if type == NodeType.LEAF:
            self.literal_str = value
    
    def __str__(self):
        if self.type == NodeType.LEAF:
            return f'{self.index} L {self.literal_str}'
        else:
            return f'{self.index} {self.type} {self.children} {self.parents} {self.mark}'

class NodeContext:
    def __init__(self):
        self.NODES: list[Node] = []
        self.ROOT: Node = self.create_node(NodeType.OR)
    
    def create_node(self, type: NodeType, value = None, mark: str = None):
        node = Node(type, len(self.NODES), value, mark)
        self.NODES.append(node)
        return node
    
    def update_NODES(self, to_remove: list[int]):
        new_NODES = []
        index_map: dict[int, int] = {} 
        for idx, node in enumerate(self.NODES):
            if idx in to_remove:
                continue
            node.index = len(new_NODES)
            index_map[idx] = node.index
            new_NODES.append(node)
        
        self.NODES = new_NODES
        for node in self.NODES:
            node.children = set(index_map[child] for child in node.children)
            node.parents = set(index_map[parent] for parent in node.parents)
    
    def split_node(self, node: Node):
        for child in node.children:
            self.NODES[child].parents.remove(node.index)
        for parent in node.parents:
            self.NODES[parent].children.remove(node.index)

    def simplify(self):
        # init parents according to the children
        for node in self.NODES:
            for child in node.children:
                self.NODES[child].parents.add(node.index)
        
        # remove the junction nodes that have no children
        to_remove = []
        for node in self.NODES:
            if node.type == NodeType.LEAF:
                continue
            if len(node.children) != 0:
                continue
            to_remove.append(node.index)
            self.split_node(node)
        self.update_NODES(to_remove)
        
        for node in self.NODES:
            print(node)
        
        # remove the node that has no parents and is not the root
        to_remove.clear()
        for node in self.NODES:
            if node.index in to_remove or node == self.ROOT:
                continue
            def dfs(node_dfs: Node):
                if len(node_dfs.parents) != 0:
                    return
                children_copy = node_dfs.children.copy()
                to_remove.append(node_dfs.index)
                self.split_node(node_dfs)
                for child in children_copy:
                    dfs(self.NODES[child])
            dfs(node)
        self.update_NODES(to_remove)
        
        # recursive remove the junction nodes that have only one child
        to_remove.clear()
        def remove_nodes_with_one_child(node: Node):
            if node.type == NodeType.LEAF:
                return
            if len(node.children) == 1:
                unique_child = next(iter(node.children))
                for parent in node.parents:
                    self.NODES[parent].children.add(unique_child)
                    self.NODES[unique_child].parents.add(parent)
                to_remove.append(node.index)
                self.split_node(node)
                remove_nodes_with_one_child(self.NODES[unique_child])
            else:
                for child in node.children:
                    remove_nodes_with_one_child(self.NODES[child])
        remove_nodes_with_one_child(self.ROOT)
        self.update_NODES(to_remove)
        
        # recursive remove the junction nodes that have the same children
        redundent_node: dict[frozenset, int] = {}
        to_remove.clear()
        def remove_nodes_with_same_children(node: Node):
            if node.type == NodeType.LEAF:
                return
            if frozenset(node.children) in redundent_node.keys() and node.index != redundent_node[frozenset(node.children)]:
                substitute_node_index = redundent_node[frozenset(node.children)]
                to_remove.append(node.index)
                for parent in node.parents:
                    self.NODES[parent].children.add(substitute_node_index)
                    self.NODES[substitute_node_index].parents.add(parent)
                self.split_node(node)
            else:
                redundent_node[frozenset(node.children)] = node.index
            for child in node.children:
                remove_nodes_with_same_children(self.NODES[child])
        
        remove_nodes_with_same_children(self.ROOT)
        self.update_NODES(to_remove)
        
        # TODO
        redundent_node: dict[frozenset, int] = {}
        to_remove.clear()
        remove_nodes_with_same_children(self.ROOT)
        self.update_NODES(to_remove)
        
        # remove the redundant junction nodes
        to_remove.clear()
        for node in self.NODES:
            if node.type == NodeType.LEAF:
                continue
            if len(node.parents) == 1:
                parent = next(iter(node.parents))
                if node.type == self.NODES[parent].type:
                    to_remove.append(node.index)
                    for child in node.children:
                        self.NODES[child].parents.add(parent)
                        self.NODES[parent].children.add(child)
                    self.split_node(node)
        self.update_NODES(to_remove)
        
        
    def show_circuit(self):
        circuit_size = 0
        gate_count = 0
        for idx, node in enumerate(self.NODES):
            circuit_size += len(node.children)
            if node.type == NodeType.AND or node.type == NodeType.OR:
                gate_count += 1
        print('Circuit size:', circuit_size)
        print(f'Node count: {len(self.NODES)}({gate_count} gates)')

        G = nx.DiGraph()

        for node in self.NODES:
            if node.type == NodeType.LEAF:
                G.add_node(str(node.index), label=node.literal_str)
            elif node.type == NodeType.AND:
                G.add_node(str(node.index), label=f'⋀({node.mark})' if node.mark is not None else '⋀')
                # G.add_node(str(node.index), label=f'⋀({node.index})')
            elif node.type == NodeType.OR:
                G.add_node(str(node.index), label=f'⋁({node.mark})' if node.mark is not None else '⋁')
                # G.add_node(str(node.index), label=f'⋁({node.index})')
            else:
                raise RuntimeError('The node type is not correct')
            
        for node in self.NODES:
            for child in node.children:
                G.add_edge(str(node.index), str(child))

        labels = nx.get_node_attributes(G, 'label')
        pos = graphviz_layout(G, prog='dot')
        plt.figure(figsize=(12, 8))
        nx.draw(G, pos,
                with_labels=True, 
                labels=labels, 
                node_color='lightblue', 
                arrows=True, 
                arrowstyle='-', 
                arrowsize=12, 
                node_size=1500, 
                font_size=10,
                verticalalignment='bottom')
        plt.tight_layout()
        plt.show()
        dot_filename = "dnnf.dot"
        nx.nx_agraph.write_dot(G, dot_filename)


NC = NodeContext()
    