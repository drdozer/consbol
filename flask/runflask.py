from flask import Flask, render_template, request, redirect, url_for, abort, session
app = Flask(__name__)

@app.route('/')
def home():
    return render_template('index.html')

@app.route('/contains')
def contains():
    return render_template('contains.html')

@app.route('/within')
def within():
    return render_template('within.html')

@app.route('/equals')
def equals():
    return render_template('equals.html')

@app.route('/contains_suffix')
def containsSuffix():
    return render_template('contains_suffix.html')

@app.route('/contains_prefix')
def containsPrefix():
    return render_template('contains_prefix.html')

@app.route('/joins_directly')
def joinsDirectly():
    return render_template('joins_directly.html')

@app.route('/joins_with_gap')
def joinsWithGap():
    return render_template('joins_with_gap.html')

@app.route('/intersects')
def intersects():
    return render_template('intersects.html')

@app.route('/strand_constraints')
def strandConstraints():
    return render_template('strand_constraints.html')

@app.route('/index_constraints')
def indexConstraints():
    return render_template('index_constraints.html')

@app.route('/length_constraints')
def lengthConstraints():
    return render_template('length_constraints.html')

if __name__ == '__main__':
    app.run("0.0.0.0",debug=True, threaded=True)
