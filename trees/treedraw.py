#!/usr/bin/python
# -*- coding: utf-8 -*-

import yapgvb, random, Image, webbrowser, sys
from datetime import datetime
import cPickle as pickle
from treeparser import treedepth
from colorspace import get_hex_colors
import time, random

colors = get_hex_colors(4, lightness=50)
colors += get_hex_colors(4, lightness=80, shift=.5)
# random.shuffle(colors)
# colors = colors*100

# colors = [	
#     (201, 130, 134),
#     (197, 135, 100),
#     (173, 146, 75),
#     (141, 156, 85),
#     (92, 163, 134),
#     (73, 163, 162),
#     (82, 158, 189),
#     (128, 149, 198),
#     (168, 138, 189),
#     (193, 131, 160)
# ]

# colors = [rgb_to_hex(x) for x in colors]

# #"#A68D00",
#           #"#439400",
#           #"#67E300",
#           #"#FFD900",
#           #"#FF6200",
#           #"#A63F00",
# #          "#FFEA73",
#           "#A9F16C",
# #          "#FFA873",
#           "#2C17B1",
#           "#E40045",
#           "#00C90D",
#           "#160773",
#           "#94002D",
#           "#008209",
#           "#7F70D8",
#           "#F16D95",
#           "#67E46F"

# ]*80

node_colors = {
    # "a" : "#A68D00",
    # "b" : "#439400",
    # "c" : "#67E300",
    # "d" : "#FFD900",
    # "e" : "#FF6200",
    # "f" : "#A63F00",
    "flip" : "#ADBBBB"
}

for (node, col) in zip(["a", "b", "c", "d", "e" ,"f"], colors):
    node_colors[node] = col

def add_node(graph, label, ncols=None):
    if not ncols:
        ncols = node_colors
    global colors
    node = graph.add_node()
    node.fillcolor = ncols.get(label) or ncols.setdefault(label, colors.pop(0))
    node.label = ''
    if label == "flip":
        node.shape = 'circle'
        node.width = node.height = 0.5
        node.penwidth = 1
        node.fillcolor = '#EFE7C6'
        node.label = '?'
    elif label == "lambda":
        node.shape = 'rectangle'
        node.width = node.height = 0.5
        node.penwidth = 1
        node.fillcolor = '#EFE7C6'
        node.label = 'λ(t)'
        # node.fontsize = 30
    elif label == "app":
        node.shape = 'circle'
        node.penwidth = 0
        # node.fontsize = 20
        node.width = node.height = 0.3
        node.label = ""
        node.fillcolor = '#ADBBBB'
    elif label == "t":
        node.shape = 'circle'
        node.penwidth = 1
        node.fillcolor = '#EFE7C6'
        node.label = 't'
    else:
        node.shape = 'circle'
        node.penwidth = 0
        node.color = 'white'
    node.style = 'filled'
    return node

def add_edge(from_node, to_node, edgewidth):
    edge = from_node >> to_node
    edge.penwidth = edgewidth
    edge.color = "#ADBBBB"

def add_subtrees(node, subtrees, graph, edgewidth=2, ncols=None):
    if not ncols:
        ncols = node_colors
    for subtree in subtrees:
        subnode_label, subchildren = subtree[0], subtree[1:]
        subnode = add_node(graph, subnode_label, ncols)
        add_edge(node, subnode, edgewidth)
        if subchildren:
            add_subtrees(subnode, subchildren, graph, edgewidth-1, ncols)

def make_thumbnail(filename, ratio=0.4):
    im = Image.open(filename)
    rim = im.resize( [int(ratio*x) for x in im.size], Image.ANTIALIAS)
    thumb_filename = filename + ".thumb.png"
    rim.save(thumb_filename)
    return thumb_filename

def tree_graph(tree, filename="tree.png", ncols=None):
    print filename
    if not ncols:
        ncols = node_colors
    graph = yapgvb.Graph("tree")
    graph.rankdir = "BT"
    graph.nodesep = 0.2
    graph.ranksep = 0.3
    root_label, subtrees = tree[0], tree[1:]
    root_node = add_node(graph, root_label, ncols)
    depth = treedepth(tree)
    add_subtrees(root_node, subtrees, graph, depth+6, ncols)
    graph.layout(yapgvb.engines.dot)
    graph.render(filename)
    graph.layout(yapgvb.engines.dot)
    graph.render(filename[:-4] + '.dot', format='dot')
    graph.render(filename[:-4] + '.pdf', format='pdf')

def show_tree(tree):
    tmp_filename = "/tmp/tree.png"
    tree_graph(tree, tmp_filename)
    thumb_filename = make_thumbnail(tmp_filename)
    tree_im = Image.open(thumb_filename)
    tree_im.show()

def forest_graph(trees, base_filename="tree-%i.png", forest_filename="forest.png"):
    x_spacing = 30
    y_spacing = 30
    filenames = [base_filename % i for i in range(len(trees))]
    thumbnames = []
    for (tree, filename) in zip(trees, filenames):
        tree_graph(tree, filename)
        thumbname = make_thumbnail(filename)
        thumbnames.append(thumbname)
    max_height = 0
    total_width = x_spacing
    thumbnails = []
    for thumbname in thumbnames:
        im = Image.open(thumbname)
        thumbnails.append(im)
        width, height = im.size
        if height > max_height:
            max_height = height
        total_width += width + x_spacing
    forest_im = Image.new("RGB", (total_width, max_height + 2*y_spacing), color="#fff")
    x = x_spacing
    for thumbnail in thumbnails:
        width, height = thumbnail.size
        y = max_height - height + y_spacing
        forest_im.paste(thumbnail, (x, y))
        x += width + x_spacing
    # ipshell()
    forest_im = forest_im.resize((int(forest_im.size[0]*0.5), int(forest_im.size[1]*0.5)), Image.ANTIALIAS)
    forest_im.save(forest_filename)

def show_forest(trees, fn=None):
    timestamp = "".join([str(a) for a in datetime.now().timetuple()])
    if not fn:
        fn = "/tmp/forest_%s.png" % (timestamp[:-2] + str(random.random())[2:])
    forest_graph(trees, base_filename="/tmp/tree-%i" + ("-%s.png" %  str(random.random()))[2:], forest_filename=fn)
    # webbrowser.open(fn)
    # print fn
    time.sleep(1)

def transform(tree):
    if type(tree) == type([]):
        if type(tree[0]) == type([]):
            return ["app"] + [transform(t) for t in tree]
        elif tree[0] == 'lambda':
            return [tree[0]] + [transform(t) for t in tree[2:]]
        else:
            return [transform(t) for t in tree]
    else:
        return tree

if __name__ == "__main__":
    
    # trees = [["a", ["b", ["c"]], ["c", ["b"]]]]
    # show_forest(trees)
    
    data = pickle.load(sys.stdin)
    if type(data[0]) == type(""):
        fn = data[0]
        trees = [transform(t) for t in data[1:]]
        show_forest(trees, fn)
    else:
        trees = [transform(t) for t in data]
        show_forest(trees)

    # trees = [transform(t) for t in [[["lambda", ["t"], ["a", ["b", ["c"]], ["c", ["t"]]]], ["flip", ["b"], ["c"]]]]]
    #trees = [["app", ["lambda", ["a", ["b", ["c"]], ["c", ["t"]]]], ["flip", ["b"], ["c"]]]]
    
    
    # graph_type = pickle.load(sys.stdin)
    # if graph_type == "forest":
    #     show_forest(trees)
    # elif graph_type == "frames":
    #     raise Exception, "not implemented yet"
