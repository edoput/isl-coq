lang.vo lang.glob lang.v.beautified lang.required_vo: lang.v 
lang.vio: lang.v 
lang.vos lang.vok lang.required_vos: lang.v 
ISL.vo ISL.glob ISL.v.beautified ISL.required_vo: ISL.v lang.vo
ISL.vio: ISL.v lang.vio
ISL.vos ISL.vok ISL.required_vos: ISL.v lang.vos
examples.vo examples.glob examples.v.beautified examples.required_vo: examples.v lang.vo ISL.vo
examples.vio: examples.v lang.vio ISL.vio
examples.vos examples.vok examples.required_vos: examples.v lang.vos ISL.vos
