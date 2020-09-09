from pprint import PrettyPrinter

print = PrettyPrinter(indent=4).pprint
item_types = ["wool","diamond", "stick", "diamond-pickaxe", "apple", "potato"
    , "rabbit", "orchid-flower", "daisy-flower", "flint", "coal", "iron-ore", "iron-ingot", "netherportal",
    "flint-and-steel"]
d = dict()
for t in item_types:
    if "-" in t:
        d[t] = t.replace("-","_")
print(d)
