.[] | select(has("result")) | .result | .[] | select(has("trace")) | .trace | .[] | select(has("value")) | .value | select(.name == "pointer") | {has_data: has("data")}
