import sphinx_rtd_theme

project = u'zlog'
source_suffix = '.rst'
master_doc = 'index'
pygments_style = 'sphinx'

html_theme = 'sphinx_rtd_theme'
html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]

html_theme_options = {
    'collapse_navigation': True,
    'display_version': True,
}

html_context = {
    'display_github': True,
    'github_user': 'noahdesu',
    'github_repo': 'zlog',
    'github_version': 'master',
    'conf_py_path': '/doc/',
}
