nola/prelude.vo nola/prelude.glob nola/prelude.v.beautified: nola/prelude.v
nola/prelude.vio: nola/prelude.v
nola/util/pred.vo nola/util/pred.glob nola/util/pred.v.beautified: nola/util/pred.v nola/prelude.vo
nola/util/pred.vio: nola/util/pred.v nola/prelude.vio
nola/util/rel.vo nola/util/rel.glob nola/util/rel.v.beautified: nola/util/rel.v nola/prelude.vo
nola/util/rel.vio: nola/util/rel.v nola/prelude.vio
nola/util/wft.vo nola/util/wft.glob nola/util/wft.v.beautified: nola/util/wft.v nola/prelude.vo nola/util/pred.vo nola/util/rel.vo
nola/util/wft.vio: nola/util/wft.v nola/prelude.vio nola/util/pred.vio nola/util/rel.vio
nola/util/list.vo nola/util/list.glob nola/util/list.v.beautified: nola/util/list.v nola/prelude.vo
nola/util/list.vio: nola/util/list.v nola/prelude.vio
nola/judg.vo nola/judg.glob nola/judg.v.beautified: nola/judg.v nola/prelude.vo nola/util/pred.vo nola/util/wft.vo
nola/judg.vio: nola/judg.v nola/prelude.vio nola/util/pred.vio nola/util/wft.vio
nola/examples/logic/ctx.vo nola/examples/logic/ctx.glob nola/examples/logic/ctx.v.beautified: nola/examples/logic/ctx.v nola/util/list.vo
nola/examples/logic/ctx.vio: nola/examples/logic/ctx.v nola/util/list.vio
nola/examples/logic/prop.vo nola/examples/logic/prop.glob nola/examples/logic/prop.v.beautified: nola/examples/logic/prop.v nola/examples/logic/ctx.vo
nola/examples/logic/prop.vio: nola/examples/logic/prop.v nola/examples/logic/ctx.vio
nola/examples/logic/subst.vo nola/examples/logic/subst.glob nola/examples/logic/subst.v.beautified: nola/examples/logic/subst.v nola/examples/logic/prop.vo
nola/examples/logic/subst.vio: nola/examples/logic/subst.v nola/examples/logic/prop.vio
nola/examples/logic/eval.vo nola/examples/logic/eval.glob nola/examples/logic/eval.v.beautified: nola/examples/logic/eval.v nola/examples/logic/subst.vo
nola/examples/logic/eval.vio: nola/examples/logic/eval.v nola/examples/logic/subst.vio
nola/examples/logic/deriv.vo nola/examples/logic/deriv.glob nola/examples/logic/deriv.v.beautified: nola/examples/logic/deriv.v nola/examples/logic/eval.vo nola/util/wft.vo nola/judg.vo
nola/examples/logic/deriv.vio: nola/examples/logic/deriv.v nola/examples/logic/eval.vio nola/util/wft.vio nola/judg.vio
nola/examples/logic/facts.vo nola/examples/logic/facts.glob nola/examples/logic/facts.v.beautified: nola/examples/logic/facts.v nola/examples/logic/deriv.vo
nola/examples/logic/facts.vio: nola/examples/logic/facts.v nola/examples/logic/deriv.vio
