// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    check_arity, eval, eval_iter_set, merge_values, svg_elem_to_string, value_to_string, EvalCtx,
    EvalError, EvalResult, Expr, FuncValue, Span, Spanned, Value,
};
use num_traits::ToPrimitive;
use std::sync::Arc;
// SVG module operators — SVGElemToString, NodeOfRingNetwork, DirectedGraphToSVG, etc.

pub(super) fn eval_builtin_svg(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === SVG Module (CommunityModules) ===
        // Animation and visualization for TLA+ specs

        // SVGElem(name, attrs, children, innerText) - create SVG element record
        "SVGElem" => {
            check_arity(name, args, 4, span)?;
            let name_val = eval(ctx, &args[0])?;
            let attrs_val = eval(ctx, &args[1])?;
            let children_val = eval(ctx, &args[2])?;
            let inner_text_val = eval(ctx, &args[3])?;
            Ok(Some(Value::record([
                ("name", name_val),
                ("attrs", attrs_val),
                ("children", children_val),
                ("innerText", inner_text_val),
            ])))
        }

        // Line(x1, y1, x2, y2, attrs) - create SVG line element
        "Line" => {
            check_arity(name, args, 5, span)?;
            let x1 = eval(ctx, &args[0])?;
            let y1 = eval(ctx, &args[1])?;
            let x2 = eval(ctx, &args[2])?;
            let y2 = eval(ctx, &args[3])?;
            let user_attrs = eval(ctx, &args[4])?;

            // Build base attrs with coordinate values as strings
            let base_attrs = Value::record([
                ("x1", Value::string(value_to_string(&x1))),
                ("y1", Value::string(value_to_string(&y1))),
                ("x2", Value::string(value_to_string(&x2))),
                ("y2", Value::string(value_to_string(&y2))),
            ]);

            // Merge: user_attrs overrides base_attrs
            let merged_attrs = merge_values(&user_attrs, &base_attrs)?;

            Ok(Some(Value::record([
                ("name", Value::string("line")),
                ("attrs", merged_attrs),
                ("children", Value::Seq(Arc::new(Vec::new().into()))),
                ("innerText", Value::string("")),
            ])))
        }

        // Circle(cx, cy, r, attrs) - create SVG circle element
        "Circle" => {
            check_arity(name, args, 4, span)?;
            let cx = eval(ctx, &args[0])?;
            let cy = eval(ctx, &args[1])?;
            let r = eval(ctx, &args[2])?;
            let user_attrs = eval(ctx, &args[3])?;

            let base_attrs = Value::record([
                ("cx", Value::string(value_to_string(&cx))),
                ("cy", Value::string(value_to_string(&cy))),
                ("r", Value::string(value_to_string(&r))),
            ]);

            let merged_attrs = merge_values(&user_attrs, &base_attrs)?;

            Ok(Some(Value::record([
                ("name", Value::string("circle")),
                ("attrs", merged_attrs),
                ("children", Value::Seq(Arc::new(Vec::new().into()))),
                ("innerText", Value::string("")),
            ])))
        }

        // Rect(x, y, w, h, attrs) - create SVG rectangle element
        "Rect" => {
            check_arity(name, args, 5, span)?;
            let x = eval(ctx, &args[0])?;
            let y = eval(ctx, &args[1])?;
            let w = eval(ctx, &args[2])?;
            let h = eval(ctx, &args[3])?;
            let user_attrs = eval(ctx, &args[4])?;

            let base_attrs = Value::record([
                ("x", Value::string(value_to_string(&x))),
                ("y", Value::string(value_to_string(&y))),
                ("width", Value::string(value_to_string(&w))),
                ("height", Value::string(value_to_string(&h))),
            ]);

            let merged_attrs = merge_values(&user_attrs, &base_attrs)?;

            Ok(Some(Value::record([
                ("name", Value::string("rect")),
                ("attrs", merged_attrs),
                ("children", Value::Seq(Arc::new(Vec::new().into()))),
                ("innerText", Value::string("")),
            ])))
        }

        // Text(x, y, text, attrs) - create SVG text element
        "Text" => {
            check_arity(name, args, 4, span)?;
            let x = eval(ctx, &args[0])?;
            let y = eval(ctx, &args[1])?;
            let text = eval(ctx, &args[2])?;
            let user_attrs = eval(ctx, &args[3])?;

            let base_attrs = Value::record([
                ("x", Value::string(value_to_string(&x))),
                ("y", Value::string(value_to_string(&y))),
            ]);

            let merged_attrs = merge_values(&user_attrs, &base_attrs)?;

            // Get text as string for innerText
            let text_str = text
                .as_string()
                .map_or_else(|| value_to_string(&text), std::string::ToString::to_string);

            Ok(Some(Value::record([
                ("name", Value::string("text")),
                ("attrs", merged_attrs),
                ("children", Value::Seq(Arc::new(Vec::new().into()))),
                ("innerText", Value::string(text_str)),
            ])))
        }

        // Image(x, y, width, height, href, attrs) - create SVG image element
        "Image" => {
            check_arity(name, args, 6, span)?;
            let x = eval(ctx, &args[0])?;
            let y = eval(ctx, &args[1])?;
            let width = eval(ctx, &args[2])?;
            let height = eval(ctx, &args[3])?;
            let href = eval(ctx, &args[4])?;
            let user_attrs = eval(ctx, &args[5])?;

            let href_str = href
                .as_string()
                .map_or_else(|| value_to_string(&href), std::string::ToString::to_string);

            let base_attrs = Value::record([
                ("x", Value::string(value_to_string(&x))),
                ("y", Value::string(value_to_string(&y))),
                ("width", Value::string(value_to_string(&width))),
                ("height", Value::string(value_to_string(&height))),
                ("href", Value::string(href_str)),
            ]);

            let merged_attrs = merge_values(&user_attrs, &base_attrs)?;

            Ok(Some(Value::record([
                ("name", Value::string("image")),
                ("attrs", merged_attrs),
                ("children", Value::Seq(Arc::new(Vec::new().into()))),
                ("innerText", Value::string("")),
            ])))
        }

        // Group(children, attrs) - create SVG group element
        "Group" => {
            check_arity(name, args, 2, span)?;
            let children = eval(ctx, &args[0])?;
            let attrs = eval(ctx, &args[1])?;

            Ok(Some(Value::record([
                ("name", Value::string("g")),
                ("attrs", attrs),
                ("children", children),
                ("innerText", Value::string("")),
            ])))
        }

        // Svg(children, attrs) - create SVG container element
        "Svg" => {
            check_arity(name, args, 2, span)?;
            let children = eval(ctx, &args[0])?;
            let attrs = eval(ctx, &args[1])?;

            Ok(Some(Value::record([
                ("name", Value::string("svg")),
                ("attrs", attrs),
                ("children", children),
                ("innerText", Value::string("")),
            ])))
        }

        // SVGDoc(children, vbX, vbY, vbW, vbH, attrs) - create full SVG document
        "SVGDoc" => {
            check_arity(name, args, 6, span)?;
            let children = eval(ctx, &args[0])?;
            let vb_x = eval(ctx, &args[1])?;
            let vb_y = eval(ctx, &args[2])?;
            let vb_w = eval(ctx, &args[3])?;
            let vb_h = eval(ctx, &args[4])?;
            let user_attrs = eval(ctx, &args[5])?;

            // Build viewBox string
            let view_box = format!(
                "{} {} {} {}",
                value_to_string(&vb_x),
                value_to_string(&vb_y),
                value_to_string(&vb_w),
                value_to_string(&vb_h)
            );

            // SVG namespace attributes
            let base_attrs = Value::record([
                ("xmlns:xlink", Value::string("http://www.w3.org/1999/xlink")),
                ("xmlns", Value::string("http://www.w3.org/2000/svg")),
                ("viewBox", Value::string(view_box)),
            ]);

            let merged_attrs = merge_values(&user_attrs, &base_attrs)?;

            // Wrap children in sequence if not already
            let children_seq = match children {
                Value::Seq(_) => children,
                _ => Value::Seq(Arc::new(vec![children].into())),
            };

            Ok(Some(Value::record([
                ("name", Value::string("svg")),
                ("attrs", merged_attrs),
                ("children", children_seq),
                ("innerText", Value::string("")),
            ])))
        }

        // SVGElemToString(elem) - convert SVG element record to string
        // elem is a record [name |-> String, attrs |-> Record, children |-> Seq, innerText |-> String]
        "SVGElemToString" => {
            check_arity(name, args, 1, span)?;
            let elem = eval(ctx, &args[0])?;
            let svg_str = svg_elem_to_string(&elem, span)?;
            Ok(Some(Value::string(svg_str)))
        }

        // NodeOfRingNetwork(cx, cy, r, n, m) - calculate coordinates for node n of m in a ring
        // Returns [x |-> Int, y |-> Int]
        "NodeOfRingNetwork" => {
            check_arity(name, args, 5, span)?;
            let cx_val = eval(ctx, &args[0])?;
            let cy_val = eval(ctx, &args[1])?;
            let r_val = eval(ctx, &args[2])?;
            let n_val = eval(ctx, &args[3])?;
            let m_val = eval(ctx, &args[4])?;

            let cx = cx_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &cx_val, Some(args[0].span)))?
                .to_i64()
                .unwrap_or(0);
            let cy = cy_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &cy_val, Some(args[1].span)))?
                .to_i64()
                .unwrap_or(0);
            let r = r_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &r_val, Some(args[2].span)))?
                .to_i64()
                .unwrap_or(0);
            let n = n_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &n_val, Some(args[3].span)))?
                .to_i64()
                .unwrap_or(0);
            let m = m_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &m_val, Some(args[4].span)))?
                .to_i64()
                .unwrap_or(1);

            // Calculate position on ring: angle = (2 * PI / m) * n
            use std::f64::consts::PI;
            let angle = if m == 0 {
                0.0
            } else {
                (2.0 * PI / m as f64) * n as f64
            };
            let x = (cx as f64 + r as f64 * angle.cos()).round() as i64;
            let y = (cy as f64 + r as f64 * angle.sin()).round() as i64;

            Ok(Some(Value::record([
                ("x", Value::SmallInt(x)),
                ("y", Value::SmallInt(y)),
            ])))
        }

        // PointOnLine(from, to, segment) - interpolate point on line
        // from and to are [x |-> Int, y |-> Int], segment is Int
        // Returns [x |-> Int, y |-> Int] at position 1/segment along the line
        "PointOnLine" => {
            check_arity(name, args, 3, span)?;
            let from_val = eval(ctx, &args[0])?;
            let to_val = eval(ctx, &args[1])?;
            let segment_val = eval(ctx, &args[2])?;

            // Extract x,y from from record
            let from_func = from_val
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Record", &from_val, Some(args[0].span)))?;
            let from_x = from_func
                .apply(&Value::string("x"))
                .and_then(|v| v.to_bigint().map(|n| n.to_i64().unwrap_or(0)))
                .unwrap_or(0);
            let from_y = from_func
                .apply(&Value::string("y"))
                .and_then(|v| v.to_bigint().map(|n| n.to_i64().unwrap_or(0)))
                .unwrap_or(0);

            // Extract x,y from to record
            let to_func = to_val
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Record", &to_val, Some(args[1].span)))?;
            let to_x = to_func
                .apply(&Value::string("x"))
                .and_then(|v| v.to_bigint().map(|n| n.to_i64().unwrap_or(0)))
                .unwrap_or(0);
            let to_y = to_func
                .apply(&Value::string("y"))
                .and_then(|v| v.to_bigint().map(|n| n.to_i64().unwrap_or(0)))
                .unwrap_or(0);

            let segment = segment_val
                .to_bigint()
                .ok_or_else(|| EvalError::type_error("Int", &segment_val, Some(args[2].span)))?
                .to_i64()
                .unwrap_or(1);

            // Calculate interpolated point
            let x = if segment == 0 {
                from_x
            } else {
                from_x + (to_x - from_x) / segment
            };
            let y = if segment == 0 {
                from_y
            } else {
                from_y + (to_y - from_y) / segment
            };

            Ok(Some(Value::record([
                ("x", Value::SmallInt(x)),
                ("y", Value::SmallInt(y)),
            ])))
        }

        // SVGSerialize - stub for file writing (model checking doesn't write files)
        "SVGSerialize" => {
            check_arity(name, args, 3, span)?;
            // Evaluate args for side effects but don't actually write
            let _ = eval(ctx, &args[0])?;
            let _ = eval(ctx, &args[1])?;
            let _ = eval(ctx, &args[2])?;
            Ok(Some(Value::Bool(true)))
        }

        // NodesOfDirectedMultiGraph - complex graph layout, return stub
        "NodesOfDirectedMultiGraph" => {
            check_arity(name, args, 3, span)?;
            let nodes_val = eval(ctx, &args[0])?;
            let _edges_val = eval(ctx, &args[1])?;
            let _options_val = eval(ctx, &args[2])?;

            // Return a simple mapping: each node gets position (0, i*50)
            // This is a stub - proper implementation would use graph layout algorithm
            // Part of #1828: use eval_iter_set for SetPred-aware iteration.
            let nodes_iter = eval_iter_set(ctx, &nodes_val, Some(args[0].span))?;

            let mut entries: Vec<(Value, Value)> = Vec::new();
            for (i, node) in nodes_iter.enumerate() {
                let pos = Value::record([
                    ("x", Value::SmallInt(0)),
                    ("y", Value::SmallInt(i as i64 * 50)),
                ]);
                entries.push((node.clone(), pos));
            }
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
