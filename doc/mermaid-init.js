(() => {
    const darkThemes = ['ayu', 'navy', 'coal'];
    const html = document.documentElement;
    const isDark = () => darkThemes.some(theme => html.classList.contains(theme));
    const initiallyDark = isDark();
    const theme = initiallyDark ? 'dark' : 'default';
    mermaid.initialize({ startOnLoad: true, theme });

    // Reload to redraw diagrams when the effective theme changes, including
    // Auto mode and changes to the system's preferred color scheme.
    new MutationObserver(() => {
        if (isDark() !== initiallyDark) {
            window.location.reload();
        }
    }).observe(html, { attributes: true, attributeFilter: ['class'] });
})();
