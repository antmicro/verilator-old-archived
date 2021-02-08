import sys, json
json_file = json.load(sys.stdin);
for i in range(len(json_file['artifacts'])):
    if json_file['artifacts'][i]["name"] == sys.argv[1]:
        pos = i
        break
print(json_file['artifacts'][pos]["id"])
