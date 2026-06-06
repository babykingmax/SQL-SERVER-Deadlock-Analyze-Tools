import xml.etree.ElementTree as ET
import json
import html
import argparse
import sys
import os
import webbrowser
import re
import logging
from collections import Counter

logging.basicConfig(level=logging.INFO, format='%(message)s')

try:
    import sqlparse
except ImportError:
    logging.error("❌ 缺少依赖库！请先在终端运行: pip install sqlparse")
    sys.exit(1)

# ================= 1. SQL 引擎 (SARG & 格式化) =================
def format_and_highlight_sql(raw_sql, enable_format=True):
    if not raw_sql or str(raw_sql).strip() == "" or str(raw_sql).lower() == "unknown":
        return "<span style='color: gray; font-style: italic;'>[语句被 SQL Server 隐藏或未知]</span>"
    
    # 极速模式或超长SQL 防护机制
    if len(raw_sql) > 10000 or not enable_format:
        return f"<pre class='code-block' style='color:#333;'>{html.escape(raw_sql[:4000])}{' ...[超长截断]' if len(raw_sql)>4000 else ''}</pre>"
        
    formatted_sql = sqlparse.format(raw_sql, reindent=True, keyword_case='upper')
    html_output = []
    for statement in sqlparse.parse(formatted_sql):
        for token in statement.flatten():
            text = html.escape(token.value)
            t_str = str(token.ttype)
            if token.is_keyword or t_str.startswith('Token.Keyword'): html_output.append(f'<span style="color:#0000FF;font-weight:bold;">{text}</span>')
            elif t_str.startswith('Token.Literal.String'): html_output.append(f'<span style="color:#A31515;">{text}</span>')
            elif t_str.startswith('Token.Literal.Number'): html_output.append(f'<span style="color:#098658;">{text}</span>')
            elif t_str.startswith('Token.Comment'): html_output.append(f'<span style="color:#008000;font-style:italic;">{text}</span>')
            elif t_str.startswith('Token.Name.Builtin'): html_output.append(f'<span style="color:#FF00FF;">{text}</span>')
            else: html_output.append(f'<span style="color:#333;">{text}</span>')
    return f'<pre class="code-block">{"".join(html_output)}</pre>'

def analyze_sarg(sql_text):
    warnings = []
    if not sql_text or sql_text == "N/A" or str(sql_text).lower() == "unknown": return warnings
    flat_sql = re.sub(r'\s+', ' ', sql_text)
    
    if re.search(r"(?i)\bLIKE\s+N?['\"]%", flat_sql):
        warnings.append({"title": "🚫 前导模糊查询", "desc": "检测到 <code>LIKE '%...'</code>，索引彻底失效。", "solution": "改为后缀匹配或引入全文索引。"})
    func_pattern = r"(?i)\b(YEAR|MONTH|DAY|DATEPART|DATEDIFF|DATEADD|CONVERT|CAST|ISNULL|COALESCE|SUBSTRING|LEFT|RIGHT|UPPER|LOWER|RTRIM|LTRIM|LEN|CHARINDEX|PATINDEX)\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\)\s*(?:>=|<=|=|!=|<>|>|<|IN\b|LIKE\b|IS\b)"
    for match in re.finditer(func_pattern, flat_sql):
        func_name, args = match.group(1).upper(), match.group(2).strip()
        clean_args = re.sub(r"'[^']*'|@\w+|\b\d+(\.\d+)?\b|(?i)\b(varchar|nvarchar|char|nchar|int|bigint|datetime|date|dd|mm|yyyy|as)\b", "", args)
        if re.search(r"[a-zA-Z_]", clean_args):
            solution = "极其危险的日期函数致盲！请改为常量的范围边界查询 (如 <code>Col >= @T1 AND Col < @T2</code>)。" if func_name in ['DATEDIFF', 'DATEADD'] else "利用代数原理将计算转移到等号右侧。"
            warnings.append({"title": f"🚫 标量函数致盲 ({func_name})", "desc": f"对潜在列或表达式 <code>{html.escape(args[:30])}</code> 使用了 <code>{func_name}()</code> 函数。", "solution": solution})
    if re.search(r"(?i)(\bNOT\s+IN\s*\(|!=|<>)", flat_sql):
        warnings.append({"title": "⚠️ 负向查询风险", "desc": "使用了 <code>!=</code> 或 <code>NOT IN</code>，极易触发大规模全表范围锁。", "solution": "尽量转化为正向查询 (如 <code>IN</code>, <code>=</code>)。"})
    
    unique_warnings = []
    seen = set()
    for w in warnings:
        if w['title'] not in seen:
            seen.add(w['title']); unique_warnings.append(w)
    return unique_warnings

def extract_db_and_table(obj_name):
    """提取数据库名与纯净表名，用于生成原生系统排查指令"""
    if not obj_name or 'unknown' in str(obj_name).lower(): return '', 'UnknownTable'
    parts = obj_name.split('.')
    db_name = parts[0] if len(parts) >= 3 else ''
    
    if len(parts) >= 2 and parts[-1].upper().startswith(('PK_', 'IX_', 'UK_', 'UQ_', 'IDX_')): 
        candidate = parts[-2]
        if candidate.lower() in ('dbo', 'sys'): table_name = re.sub(r'^(?i)(PK_|IX_|UK_|UQ_|IDX_)', '', parts[-1])
        else: table_name = candidate.split('.')[-1] if '.' in candidate else candidate
    else:
        table_name = parts[-1] if len(parts) >= 2 else parts[0]
    return db_name, table_name

# ================= 2. 深度内核解析 (引入 Parallel 并行判定) =================
def parse_single_deadlock(dl_xml_str, dl_index, enable_format=True):
    try: root = ET.fromstring(dl_xml_str)
    except: return None
    
    times = [p.get('lastbatchstarted') or p.get('lasttranstarted') for p in root.findall('.//process-list/process')]
    dl_time = max([t for t in times if t]).replace('T', ' ') if any(times) else f"批量死锁事件 #{dl_index}"

    victim_node = root.find('.//victim-list/victimProcess')
    victim_id = victim_node.get('id') if victim_node is not None else None

    nodes, edges, resources_data = [], [], []
    process_dict = {}
    
    # 【核心】并行特征提取
    spids = []
    is_parallel = False

    for p in root.findall('.//process-list/process'):
        p_id, spid, ecid = p.get('id'), p.get('spid', 'Unknown'), p.get('ecid', '0')
        if spid != 'Unknown': spids.append(spid)
        if ecid != '0': is_parallel = True # 如果存在工作线程 ID (ecid > 0)，铁定是并行引发
        
        inputbuf = p.find('.//inputbuf')
        raw_sql = inputbuf.text.strip() if inputbuf is not None and inputbuf.text else "N/A"
        
        frames = [{'procname': f.get('procname') or 'Unknown', 'line': f.get('line') or '?', 'stmt': f.text.strip() if f.text else ""} 
                  for f in (p.findall('.//executionStack/frame') or [])]
        active_sql = next((f['stmt'] for f in frames if f['stmt'] and f['stmt'].lower()!='unknown'), raw_sql)

        html_blocks = []
        if frames:
            for i, f in enumerate(frames):
                stmt = f['stmt']
                hl = "<div style='color:gray; font-size:12px; margin-bottom:5px;'>[该层语句被隐藏或脱靶 (Unknown)]</div>" + (format_and_highlight_sql(raw_sql, enable_format) if i==0 and raw_sql!="N/A" else "") if not stmt or stmt.lower()=='unknown' else format_and_highlight_sql(stmt, enable_format)
                html_blocks.append(f"<div style='margin-bottom:10px; border-left:4px solid {'#e74c3c' if i==0 else '#95a5a6'}; padding:10px; background:{'#fff2f0' if i==0 else '#f9f9f9'}; border-radius:4px;'><b>{'📍 报错最内层' if i==0 else '⤴️ 外层调用'} | <code>{html.escape(f['procname'])}</code></b><br>{hl}</div>")
        
        if raw_sql and raw_sql != "N/A": 
            html_blocks.append(f"<div style='margin-bottom:10px; border-left:4px solid #3498db; padding:10px; background:#f0f8ff; border-radius:4px;'><b>📥 客户端请求 (Input Buffer):</b><br>{format_and_highlight_sql(raw_sql, enable_format)}</div>")

        sarg_warns = analyze_sarg(active_sql)
        if raw_sql != "N/A":
            for w in analyze_sarg(raw_sql):
                if not any(x['title'] == w['title'] for x in sarg_warns): sarg_warns.append(w)
        
        is_victim = (p_id == victim_id)
        process_dict[p_id] = is_victim
        nodes.append({"id": p_id, "label": f"SPID: {spid}{' (并行线程 ECID:'+ecid+')' if ecid!='0' else ''}", "shape": "ellipse", "color": "#ff4d4d" if is_victim else "#4da6ff", "isProcess": True, "spidInfo": spid, "html_sql": "".join(html_blocks) or "无语句", "sarg_warnings": sarg_warns})

    # 【核心】SPID 重复检测与 CXPACKET 资源检测
    if len(spids) > 0 and len(set(spids)) < len(spids): is_parallel = True
    if root.find('.//exchangeEvent') is not None or root.find('.//threadpool') is not None: is_parallel = True

    res_idx = 1
    for res_list in root.findall('.//resource-list'):
        for res in res_list:
            res_type, obj_name = res.tag, res.get('objectname', '')
            if is_parallel and ('exchangeEvent' in res_type or 'threadpool' in res_type): obj_name = f"{res_type} 并行数据交换管道等待"
            if not obj_name: obj_name = f"Unknown (HobtID: {res.get('associatedObjectId') or res.get('hobtid')})"
            res_id = f"{res_type}_{res_idx}"
            res_idx += 1
            
            db_name, clean_table = extract_db_and_table(obj_name)
            nodes.append({"id": res_id, "label": f"[{res_type}]\n{html.escape(clean_table)}", "shape": "box", "color": "#f39c12", "isProcess": False, "title": html.escape(obj_name)})
            
            for o in res.findall('.//owner-list/owner'): edges.append({"from": res_id, "to": o.get('id'), "label": f"Owns: {o.get('mode')}", "color": {"color": "#27ae60"}, "arrows": "to"})
            for w in res.findall('.//waiter-list/waiter'): edges.append({"from": w.get('id'), "to": res_id, "label": f"Waits: {w.get('requestType', w.get('mode'))}", "color": {"color": "#ff0000" if process_dict.get(w.get('id')) else "#c0392b"}, "arrows": "to", "dashes": True, "width": 3.5 if process_dict.get(w.get('id')) else 1.2})
            resources_data.append({"obj": obj_name, "db": db_name, "clean_table": clean_table})

    diag_type, diag_title, diag_desc = "Unknown", "未知复杂死锁", "未命中经典规则，请结合执行计划人工排查。"
    valid_tables = list(set([r['clean_table'] for r in resources_data if r['clean_table'] != 'UnknownTable']))
    
    if is_parallel:
        diag_type, diag_title = "Parallel", "⚡ 并行死锁 (Intra-Query Parallelism)"
        diag_desc = "发生于同一个复杂查询内的多个并行线程之间 (如 CXPACKET/CXCONSUMER 等待)。<br><b>👉 调优闭环指南：</b>此类死锁修改索引往往南辕北辙。请考虑在查询末尾添加 <code>OPTION (MAXDOP 1)</code> 降级并行度，或调高实例级别的 <code>Cost Threshold for Parallelism</code> 参数。"
    elif len(set(valid_tables)) <= 1 and len(resources_data) >= 2:
        if any("IX_" in r['obj'].upper() or "PK_" in r['obj'].upper() for r in resources_data):
            diag_type, diag_title = "Bookmark Lookup", "🔖 书签查找死锁"
            diag_desc = "针对同一张表的不同索引(聚集/非聚集)发生交叉争用。<br><b>👉 调优闭环指南：</b>请检查右侧 SARG 并为该查询涉及的列补齐 <code>INCLUDE</code> 覆盖索引避免回表。"
        else:
            diag_type, diag_title = "Intra-Table", "📄 单表交叉死锁 (Intra-Table)"
            diag_desc = "单表范围扫描锁升级导致交叉。<br><b>👉 调优闭环指南：</b>极其重点排查右侧 SARG 警告，这通常意味着原本应走索引的列被函数致盲导致全表锁闭。"
    elif len(set(valid_tables)) > 1:
        diag_type, diag_title = "Reverse Order", "🔄 反向顺序交叉 (Reverse Order)"
        diag_desc = "应用层代码对多张表进行了乱序写入/读取访问。<br><b>👉 调优闭环指南：</b>请规范并强制开发在存储过程或事务中，以绝对一致的相同顺序去操作表对象。"
    elif len(resources_data) == 1:
        diag_type, diag_title = "Conversion", "⚡ 锁转换死锁 (Conversion Deadlock)"
        diag_desc = "高并发下，进程持有了 S 读锁并同时尝试升级为 X 写锁。<br><b>👉 调优闭环指南：</b>在初始 SELECT 查询中显式加入 <code>WITH (UPDLOCK)</code> 让更新串行化排队。"

    advise_cmd = ""
    if valid_tables and not is_parallel:
        db_name = next((r['db'] for r in resources_data if r['clean_table'] == valid_tables[0] and r['db']), '')
        db_prefix = f"USE [{db_name}]; " if db_name else ""
        # 使用 SQL Server 内置原生指令
        advise_cmd = f"{db_prefix}EXEC sp_helpindex '{valid_tables[0]}';"

    return {
        "index": dl_index, "time": dl_time, "type": diag_type, "title": diag_title, "desc": diag_desc,
        "advise_cmd": advise_cmd, "resources": resources_data, "tables": valid_tables, "nodes": nodes, "edges": edges
    }

# ================= 3. 大盘生成器 (Batch & Dashboard) =================
def process_batch(input_path, output_html, enable_format):
    logging.info(f"🔍 正在检索输入路径: {input_path}")
    files = []
    if os.path.isdir(input_path):
        for f in os.listdir(input_path):
            if f.lower().endswith(('.xdl', '.xml', '.xel')):
                files.append(os.path.join(input_path, f))
    else:
        files.append(input_path)

    parsed_deadlocks = []
    idx = 1
    
    # 特征：剥离引擎（免疫 XE 杂乱日志文本或多个合并的 XML）
    for fpath in files:
        try:
            with open(fpath, 'r', encoding='utf-8', errors='ignore') as f:
                content = re.sub(r'\sxmlns(:\w+)?="[^"]+"', '', f.read())
                matches = re.finditer(r'<deadlock.*?</deadlock>', content, re.DOTALL | re.IGNORECASE)
                for m in matches:
                    dl = parse_single_deadlock(m.group(0), idx, enable_format)
                    if dl:
                        parsed_deadlocks.append(dl)
                        idx += 1
        except Exception as e:
            logging.error(f"⚠️ 跳过异常文件 {fpath}: {e}")

    if not parsed_deadlocks:
        logging.error("❌ 未找到任何有效的 <deadlock> 数据！")
        return False

    logging.info(f"✅ 成功提取并解析 {len(parsed_deadlocks)} 个死锁！正在构建 DEADLOCK ANALYZE TOOLS 大盘...")

    type_counts = Counter([d['type'] for d in parsed_deadlocks])
    date_counts = Counter([d['time'][:10] for d in parsed_deadlocks if d['time'] != 'Unknown Time'])
    sorted_dates = sorted(date_counts.keys())
    trend_labels = sorted_dates
    trend_data = [date_counts[k] for k in sorted_dates]

    table_counts = Counter()
    for d in parsed_deadlocks:
        for r in d['resources']:
            if r['clean_table'] != 'UnknownTable' and not 'exchangeEvent' in r['obj']:
                table_counts[(r['db'], r['clean_table'])] += 1
                
    top_tables = table_counts.most_common(5)
    max_tbl_cnt = top_tables[0][1] if top_tables else 1

    automation_hint = ""
    if top_tables:
        t_db = top_tables[0][0][0]
        t_tb = top_tables[0][0][1]
        use_db_stmt = f"USE [{t_db}]; " if t_db else ""
        automation_hint = f"<div style='margin-top:20px; padding:15px; background:#eafaf1; border:1px solid #c3e6cb; border-radius:6px; color:#27ae60; font-size:13px; line-height:1.6;'><b>💡 DEADLOCK ANALYZE TOOLS 自动化闭环指令：</b><br>强烈建议针对最高频热点表 <b>{t_tb}</b> 执行系统原生语句排查缺失索引和碎片：<br><code style='background:#fff; padding:3px 6px; border-radius:3px; color:#c0392b; display:inline-block; margin-top:5px; border:1px solid #e1e1e1;'>{use_db_stmt}EXEC sp_helpindex '{t_tb}';</code></div>"

    html_template = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="utf-8"><title>SQL Server 死锁监控大盘 (DEADLOCK ANALYZE TOOLS)</title>
        <script type="text/javascript" src="https://unpkg.com/vis-network@9.1.9/standalone/umd/vis-network.min.js"></script>
        <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
        <style>
            :root {{ --primary: #1e2b3c; --accent: #3498db; --danger: #e74c3c; }}
            body {{ font-family: 'Segoe UI', Tahoma, sans-serif; margin: 0; background: #f4f6f8; display: flex; height: 100vh; overflow: hidden; }}
            
            .sidebar {{ width: 280px; background: var(--primary); color: white; display: flex; flex-direction: column; overflow-y: auto; z-index: 10; box-shadow: 2px 0 6px rgba(0,0,0,0.1);}}
            .sidebar-header {{ padding: 20px; background: #141d29; border-bottom: 1px solid #2c3e50; }}
            .sidebar-header h2 {{ margin: 0; font-size: 18px; color: #fff; line-height: 1.4; }}
            .sidebar-header p {{ margin: 5px 0 0; font-size: 12px; color: #7f8c8d; }}
            
            .menu-item {{ padding: 15px 20px; cursor: pointer; border-bottom: 1px solid #2c3e50; transition: 0.2s; display: flex; flex-direction: column; }}
            .menu-item:hover {{ background: #2c3e50; }}
            .menu-item.active {{ background: var(--accent); border-left: 4px solid #fff; }}
            .menu-time {{ font-size: 12px; color: #aab7c4; margin-bottom: 5px; }}
            .menu-type {{ font-size: 14px; font-weight: bold; }}
            
            .main-content {{ flex: 1; display: flex; flex-direction: column; overflow: hidden; padding: 20px; gap: 20px; }}
            
            /* 大屏监控 UI */
            #dashboard-view {{ display: flex; flex-direction: column; gap: 20px; overflow-y: auto; height: 100%; }}
            .dash-row {{ display: flex; gap: 20px; }}
            .dash-card {{ background: white; border-radius: 8px; padding: 20px; box-shadow: 0 2px 6px rgba(0,0,0,0.05); flex: 1; border-top: 4px solid var(--accent); }}
            .dash-title {{ font-size: 16px; font-weight: bold; color: #2c3e50; margin-bottom: 15px; padding-bottom: 10px; border-bottom: 1px solid #eee; }}
            
            .bar-row {{ display: flex; align-items: center; margin-bottom: 12px; }}
            .bar-label {{ width: 150px; font-size: 13px; color: #333; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }}
            .bar-track {{ flex: 1; background: #eee; height: 16px; border-radius: 8px; overflow: hidden; margin: 0 15px; }}
            .bar-fill {{ height: 100%; transition: width 0.5s ease; }}
            .bar-val {{ width: 40px; font-weight: bold; font-size: 13px; color: #555; text-align: right; }}
            
            /* 单例详情 UI */
            #deadlock-view {{ display: none; height: 100%; flex-direction: column; gap: 20px; }}
            .diag-panel {{ background: white; padding: 20px; border-radius: 8px; box-shadow: 0 2px 6px rgba(0,0,0,0.05); border-left: 5px solid var(--accent); flex-shrink: 0; }}
            .diag-panel h3 {{ margin: 0 0 8px 0; color: #2c3e50; }}
            
            .panels-container {{ display: flex; gap: 20px; flex: 1; min-height: 0; }}
            .graph-box {{ flex: 5.5; background: white; border-radius: 8px; border: 1px solid #ddd; position: relative; box-shadow: 0 2px 6px rgba(0,0,0,0.05); overflow: hidden;}}
            #mynetwork {{ width: 100%; height: 100%; outline: none; }}
            
            .code-box {{ flex: 4.5; display: flex; flex-direction: column; gap: 15px; overflow: hidden; }}
            .sarg-box, .sql-box {{ background: white; border-radius: 8px; border: 1px solid #ddd; display: flex; flex-direction: column; overflow: hidden; box-shadow: 0 2px 6px rgba(0,0,0,0.05); }}
            .box-header {{ background: #fafafa; padding: 12px 15px; font-weight: bold; border-bottom: 1px solid #ddd; font-size: 14px; display: flex; justify-content: space-between; align-items: center;}}
            .box-body {{ padding: 15px; overflow-y: auto; font-size: 13.5px; flex: 1; }}
            
            .sarg-item {{ padding: 10px; margin-bottom: 10px; border-left: 4px solid var(--danger); background: #fff5f5; border-radius: 0 4px 4px 0; }}
            pre.code-block {{ margin: 0; font-family: Consolas, monospace; font-size: 13.5px; line-height: 1.5; white-space: pre-wrap; }}
        </style>
    </head>
    <body>
        <div class="sidebar">
            <div class="sidebar-header">
                <h2>⚡ DEADLOCK ANALYZE TOOLS<br>监控站</h2>
                <p>提取完毕：共 {len(parsed_deadlocks)} 个事件</p>
            </div>
            <div class="menu-item active" id="menu-dash" onclick="showDashboard()">
                <div style="font-size:16px;">📊 全局统计监控大盘</div>
                <div class="menu-time" style="margin-top:5px;">宏观分析与调优指南</div>
            </div>
            {"".join([f"<div class='menu-item' id='menu-dl-{i}' onclick='showDeadlock({i})'><div class='menu-time'>🕒 {d['time']}</div><div class='menu-type' style='color:{'#f39c12' if 'Parallel' in d['type'] else '#fff'};'>{d['type']}</div></div>" for i, d in enumerate(parsed_deadlocks)])}
        </div>
        
        <div class="main-content">
            <div id="dashboard-view">
                <div class="dash-row">
                    <div class="dash-card" style="border-top-color: #27ae60;">
                        <div class="dash-title">📈 死锁发生趋势 (按天聚合)</div>
                        <div style="height: 250px;"><canvas id="trendChart"></canvas></div>
                    </div>
                    <div class="dash-card" style="border-top-color: var(--accent);">
                        <div class="dash-title">🎯 死锁诊断类型全局分布</div>
                        <div style="height: 250px;"><canvas id="typeChart"></canvas></div>
                    </div>
                </div>
                
                <div class="dash-row">
                    <div class="dash-card" style="border-top-color: var(--danger);">
                        <div class="dash-title">🔥 Top N 矛盾重灾区 (建议应用二八定律调优)</div>
                        {"".join([f"<div class='bar-row'><div class='bar-label' title='{k[1]}'>[{k[0]}]<br><b>{k[1]}</b></div><div class='bar-track'><div class='bar-fill' style='width: {(v/max_tbl_cnt)*100}%; background: var(--danger);'></div></div><div class='bar-val'>{v}次</div></div>" for k, v in top_tables]) if top_tables else "<div style='color:#777; padding:10px;'>此批死锁未提取到有效的用户业务表。</div>"}
                        
                        {automation_hint}
                    </div>
                </div>
            </div>

            <div id="deadlock-view">
                <div class="diag-panel">
                    <h3 id="dl-title">标题</h3>
                    <div id="dl-desc" style="color:#555; font-size:14.5px; line-height:1.6;"></div>
                    <div id="dl-advise" style="display:none; margin-top:10px; padding:10px; background:#eafaf1; border:1px solid #c3e6cb; color:#155724; border-radius:4px; font-family:monospace; font-weight:bold;"></div>
                </div>
                
                <div class="panels-container">
                    <div class="graph-box">
                        <div style="position:absolute; top:10px; left:10px; z-index:10; background:rgba(255,255,255,0.95); padding:10px; border:1px solid #ddd; font-size:12px; border-radius:6px; pointer-events:none; line-height:1.5;">
                            <b>图例说明：</b><br>🔴 牺牲进程 🔵 存活进程 🟨 锁资源<br>
                            <span style="color:#27ae60">━━▶</span> 持有锁 (Owns)<br><span style="color:#e74c3c">- - ▶</span> 请求锁 (Waits)
                        </div>
                        <div id="mynetwork"></div>
                    </div>
                    
                    <div class="code-box">
                        <div class="sarg-box" style="flex: 0 0 auto;">
                            <div class="box-header" style="background:#fff3cd; color:#856404;">⚡ SARG 索引合规扫描 (点击左图进程触发)</div>
                            <div class="box-body" id="sarg-body" style="max-height: 250px;"><div style="color:#999;text-align:center;">👈 请在左侧图中选择一个进程节点</div></div>
                        </div>
                        <div class="sql-box" style="flex: 1;">
                            <div class="box-header"><span>📝 深度调用堆栈 (Call Stack)</span> <span id="sql-spid" style="color:var(--accent);"></span></div>
                            <div class="box-body" id="sql-body"><div style="color:#999;text-align:center;margin-top:20px;">👈 请点击左侧图谱中的进程节点。</div></div>
                        </div>
                    </div>
                </div>
            </div>
        </div>

        <script type="text/javascript">
            // --- Chart.js 渲染 ---
            new Chart(document.getElementById('trendChart'), {{
                type: 'line', data: {{ labels: {json.dumps(trend_labels)}, datasets: [{{ label: '死锁发生频次', data: {json.dumps(trend_data)}, borderColor: '#27ae60', backgroundColor: 'rgba(39, 174, 96, 0.1)', fill: true, tension: 0.3 }}] }},
                options: {{ maintainAspectRatio: false, scales: {{ y: {{ beginAtZero: true, ticks: {{ stepSize: 1 }} }} }} }}
            }});
            new Chart(document.getElementById('typeChart'), {{
                type: 'doughnut', data: {{ labels: {json.dumps(list(type_counts.keys()))}, datasets: [{{ data: {json.dumps(list(type_counts.values()))}, backgroundColor: ['#3498db', '#e74c3c', '#f39c12', '#9b59b6', '#34495e'] }}] }},
                options: {{ maintainAspectRatio: false, plugins: {{ legend: {{ position: 'right' }} }} }}
            }});

            // --- 页面逻辑渲染 ---
            var allData = {json.dumps(parsed_deadlocks, ensure_ascii=False)};
            var network = null;

            function clearMenu() {{ document.querySelectorAll('.menu-item').forEach(e => e.classList.remove('active')); }}

            function showDashboard() {{
                clearMenu();
                document.getElementById('menu-dash').classList.add('active');
                document.getElementById('dashboard-view').style.display = 'flex';
                document.getElementById('deadlock-view').style.display = 'none';
            }}

            function showDeadlock(index) {{
                clearMenu();
                document.getElementById('menu-dl-' + index).classList.add('active');
                document.getElementById('dashboard-view').style.display = 'none';
                document.getElementById('deadlock-view').style.display = 'flex';
                
                var data = allData[index];
                document.getElementById('dl-title').innerHTML = "诊断：" + data.title;
                document.getElementById('dl-desc').innerHTML = data.desc;
                
                var adviseDiv = document.getElementById('dl-advise');
                if(data.advise_cmd) {{ adviseDiv.style.display = 'block'; adviseDiv.innerHTML = "💡 原生指令联动建议：<br>" + data.advise_cmd; }} 
                else {{ adviseDiv.style.display = 'none'; }}
                
                document.getElementById('sql-spid').innerHTML = "";
                document.getElementById('sql-body').innerHTML = "<div style='color:#999;text-align:center;margin-top:20px;'>👈 请点击左侧图谱中的进程节点。</div>";
                document.getElementById('sarg-body').innerHTML = "<div style='color:#999;text-align:center;'>等待选择...</div>";

                if (network) network.destroy();
                var container = document.getElementById('mynetwork');
                var visData = {{ nodes: new vis.DataSet(data.nodes), edges: new vis.DataSet(data.edges) }};
                network = new vis.Network(container, visData, {{
                    physics: {{ solver: 'hierarchicalRepulsion', hierarchicalRepulsion: {{ nodeDistance: 220, springLength: 150 }} }},
                    edges: {{ smooth: {{ type: 'curvedCW', roundness: 0.2 }} }},
                    interaction: {{ hover: true }}
                }});

                network.on("click", function(p) {{
                    if(p.nodes.length > 0) {{
                        var n = visData.nodes.get(p.nodes[0]);
                        if(n.isProcess) {{
                            document.getElementById('sql-spid').innerHTML = "- " + n.label.split('\\n')[0] + (n.color === "#ff4d4d" ? " <span style='color:red;'>(牺牲品)</span>" : "");
                            document.getElementById('sql-body').innerHTML = n.html_sql;
                            
                            if (data.type === "Parallel") {{
                                document.getElementById('sarg-body').innerHTML = "<div style='padding:15px; background:#fdf2e9; border:1px solid #e67e22; border-radius:4px; color:#d35400; font-weight:bold;'>⛔ 这是一个并行死锁 (Parallel Deadlock)！<br>查询语句内的多线程互锁。无需关心 SARG，请直接去调优实例或查询级别的 MAXDOP 并行度。</div>";
                            }} else if (n.sarg_warnings && n.sarg_warnings.length > 0) {{
                                document.getElementById('sarg-body').innerHTML = n.sarg_warnings.map(w => `<div class='sarg-item'><b style='color:#c0392b;'>${{w.title}}</b><br><span style='color:#555'>${{w.desc}}</span><br><div style='margin-top:5px;color:#27ae60'><b>👉 建议：</b>${{w.solution}}</div></div>`).join('');
                            }} else {{
                                document.getElementById('sarg-body').innerHTML = "<div style='background:#eafaf1; border:1px solid #c3e6cb; padding:15px; color:#27ae60; border-radius:4px; text-align:center;'><b>✅ SARG 扫描安全通过</b></div>";
                            }}
                        }} else {{
                            document.getElementById('sql-spid').innerHTML = "- 资源节点";
                            document.getElementById('sql-body').innerHTML = "<div style='padding:20px; font-weight:bold;'>" + n.title + "</div>";
                            document.getElementById('sarg-body').innerHTML = "<div style='color:#999;text-align:center;'>// 锁资源无代码</div>";
                        }}
                    }}
                }});
            }}
        </script>
    </body>
    </html>
    """
    with open(output_html, "w", encoding="utf-8") as f: f.write(html_template)
    logging.info(f"✅ DEADLOCK ANALYZE TOOLS 大屏生成完毕！文件存放于: {os.path.abspath(output_html)}")
    return True

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="🚀 SQL Server 全场景死锁监控大屏 (DEADLOCK ANALYZE TOOLS V8)")
    parser.add_argument("input_path", nargs='?', help="支持三种模式：1. 单个 .xdl/.xml 2. 整个包含了日志的文件夹 3. 包含大量死锁的 XEL导出XML文件")
    parser.add_argument("-o", "--output", default="Deadlock_Analyze_Tools_Dashboard.html")
    parser.add_argument("--fast", action="store_true", help="【极速批处理】关闭后端 SQL 高亮排版，可使 100+ 个死锁的渲染时间从几十秒缩短至 1 秒")
    parser.add_argument("--no-browser", action="store_true")
    args = parser.parse_args()

    if args.input_path:
        process_batch(args.input_path, args.output, not args.fast)
        if not args.no_browser: webbrowser.open(f"file://{os.path.abspath(args.output)}")
    else:
        logging.info("💡 演示模式：正在模拟 Extended Events 导出的巨大日志文件 (包含 并行死锁 与 书签死锁)...")
        # 演示环境：模拟直接从 XE 里导出合并的多个死锁 XML
        demo_xe_log = """
        <root>
          <deadlock><victim-list><victimProcess id="p1" /></victim-list>
          <process-list>
            <process id="p1" spid="88" ecid="1" lastbatchstarted="2026-06-05T08:00:00"><inputbuf>SELECT SUM(amount) FROM Orders o JOIN BigTable b ON o.id=b.id OPTION(MAXDOP 8)</inputbuf></process>
            <process id="p2" spid="88" ecid="2" lastbatchstarted="2026-06-05T08:00:00"></process>
          </process-list>
          <resource-list>
            <exchangeEvent id="e1"><owner-list><owner id="p2"/></owner-list><waiter-list><waiter id="p1"/></waiter-list></exchangeEvent>
            <exchangeEvent id="e2"><owner-list><owner id="p1"/></owner-list><waiter-list><waiter id="p2"/></waiter-list></exchangeEvent>
          </resource-list></deadlock>

          <deadlock><victim-list><victimProcess id="p3" /></victim-list>
          <process-list>
            <process id="p3" spid="111" ecid="0" lastbatchstarted="2026-06-06T09:30:15"><inputbuf>UPDATE AppDB.dbo.Users SET Role=1 WHERE DATEDIFF(dd, JoinDate, GETDATE()) = 0</inputbuf></process>
            <process id="p4" spid="222" ecid="0" lastbatchstarted="2026-06-06T09:30:15"><inputbuf>SELECT Name FROM AppDB.dbo.Users WHERE Age = 25</inputbuf></process>
          </process-list>
          <resource-list>
            <keylock objectname="AppDB.dbo.Users.PK_Users"><owner-list><owner id="p4" mode="S"/></owner-list><waiter-list><waiter id="p3" mode="X"/></waiter-list></keylock>
            <keylock objectname="AppDB.dbo.Users.IX_Age"><owner-list><owner id="p3" mode="X"/></owner-list><waiter-list><waiter id="p4" mode="S"/></waiter-list></keylock>
          </resource-list></deadlock>
        </root>
        """
        temp_file = "temp_xe_export.xml"
        with open(temp_file, "w") as f: f.write(demo_xe_log)
        process_batch(temp_file, args.output, not args.fast)
        os.remove(temp_file)
        if not args.no_browser: webbrowser.open(f"file://{os.path.abspath(args.output)}")